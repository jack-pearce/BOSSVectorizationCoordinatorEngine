#include <BOSS.hpp>
#include <Expression.hpp>
#include <ExpressionUtilities.hpp>
#include <Utilities.hpp>
#include <cassert>
#include <chrono>
#include <iomanip>
#include <iostream>

#include "/home/jcp122/repos/BOSSHazardAdaptiveEngine/Source/utilities/sharedDataTypes.hpp"
// #include "/repos/BOSSHazardAdaptiveEngine/Source/utilities/sharedDataTypes.hpp"

// #define DEBUG_MODE
// #define DEBUG_MODE_VERBOSE
#define FIRST_ENGINE_IS_STORAGE_ENGINE
#define HAZARD_ADAPTIVE_ENGINE_IN_PIPELINE

using std::string_literals::operator""s;
using boss::utilities::operator""_;

using boss::ComplexExpression;
using boss::Expression;
using boss::ExpressionArguments;
using boss::Span;
using boss::Symbol;
using ExpressionSpanArguments = boss::DefaultExpressionSystem::ExpressionSpanArguments;
using ExpressionSpanArgument = boss::DefaultExpressionSystem::ExpressionSpanArgument;
template <typename... T>
using ComplexExpressionWithStaticArguments =
    boss::DefaultExpressionSystem::ComplexExpressionWithStaticArguments<T...>;
using boss::expressions::CloneReason;

using evaluteFunction = BOSSExpression* (*)(BOSSExpression*);
using evaluteInternalFunction = std::function<Expression(ComplexExpression&&)>;

namespace utilities {
auto _false = ComplexExpression("False"_, {}, {}, {});
}

static ComplexExpression& getTableReference(ComplexExpression& e,
                                            ComplexExpression& _false = utilities::_false);

#ifdef DEBUG_MODE
namespace utilities {
static boss::Expression injectDebugInfoToSpans(boss::Expression&& expr) {
  return std::visit(
      boss::utilities::overload(
          [&](boss::ComplexExpression&& e) -> boss::Expression {
            auto [head, unused_, dynamics, spans] = std::move(e).decompose();
            boss::ExpressionArguments debugDynamics;
            debugDynamics.reserve(dynamics.size() + spans.size());
            std::transform(std::make_move_iterator(dynamics.begin()),
                           std::make_move_iterator(dynamics.end()),
                           std::back_inserter(debugDynamics), [](auto&& arg) {
                             return injectDebugInfoToSpans(std::forward<decltype(arg)>(arg));
                           });
            std::transform(
                std::make_move_iterator(spans.begin()), std::make_move_iterator(spans.end()),
                std::back_inserter(debugDynamics), [](auto&& span) {
                  return std::visit(
                      [](auto&& typedSpan) -> boss::Expression {
                        using Element = typename std::decay_t<decltype(typedSpan)>::element_type;
                        return boss::ComplexExpressionWithStaticArguments<std::string, int64_t>(
                            "Span"_, {typeid(Element).name(), typedSpan.size()}, {}, {});
                      },
                      std::forward<decltype(span)>(span));
                });
            return boss::ComplexExpression(std::move(head), {}, std::move(debugDynamics), {});
          },
          [](auto&& otherTypes) -> boss::Expression { return otherTypes; }),
      std::move(expr));
}
} // namespace utilities
#endif

static ComplexExpression addIdToPredicates(ComplexExpression&& expr, int& predicateCount) {
  auto [head, unused, dynamics, unused_] = std::move(expr).decompose();
  ExpressionArguments outputDynamics;
  outputDynamics.reserve(dynamics.size());
  std::transform(
      std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
      std::back_inserter(outputDynamics), [&predicateCount](auto&& arg_) -> ComplexExpression {
        auto&& arg = get<ComplexExpression>(std::forward<decltype(arg_)>(arg_));
        if(arg.getHead().getName() == "And") {
          return addIdToPredicates(std::move(arg), predicateCount);
        }
        auto [predHead, unused1, predDynamics, unused2] = std::move(arg).decompose();
        ExpressionArguments idDynamics;
        idDynamics.emplace_back(predicateCount++);
        auto idExpr = ComplexExpression("PredicateID"_, {}, std::move(idDynamics), {});
        predDynamics.emplace_back(std::move(idExpr));
        return {std::move(predHead), {}, std::move(predDynamics), {}};
      });
  return {std::move(head), {}, std::move(outputDynamics), {}};
}

/* Precondition: Currently adds an ID to all 'Where' predicates, therefore assumes that
 * only 'Select' can have 'Where' predicates. */
static ComplexExpression prepareExpressionForHazardAdaptiveEngineAux(ComplexExpression&& expr,
                                                                     int& predicateCount) {
  auto [head, unused, dynamics, unused_] = std::move(expr).decompose();
  ExpressionArguments outputDynamics;
  outputDynamics.reserve(dynamics.size());
  std::transform(std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
                 std::back_inserter(outputDynamics), [&predicateCount](auto&& arg_) -> Expression {
                   if(std::holds_alternative<ComplexExpression>(arg_)) {
                     auto&& arg = get<ComplexExpression>(std::forward<decltype(arg_)>(arg_));
                     if(arg.getHead().getName() == "Where") {
                       return addIdToPredicates(std::move(arg), predicateCount);
                     }
                     return prepareExpressionForHazardAdaptiveEngineAux(std::move(arg),
                                                                        predicateCount);
                   } else {
                     return arg_;
                   }
                 });
  return {std::move(head), {}, std::move(outputDynamics), {}};
}

static ComplexExpression prepareExpressionForHazardAdaptiveEngine(ComplexExpression&& expr) {
  int predicateCount = 0;
  expr = prepareExpressionForHazardAdaptiveEngineAux(std::move(expr), predicateCount);
#if defined(DEBUG_MODE) || defined(DEBUG_MODE_VERBOSE)
  std::cout << "Identified " << predicateCount << " Select operators" << std::endl;
#endif
  if(predicateCount > 0) {
    auto* selectOperators = new adaptive::SelectOperatorStates(predicateCount);
    ExpressionArguments statsArgs;
    statsArgs.emplace_back(reinterpret_cast<int64_t>(selectOperators));
    auto stats = ComplexExpression("Stats"_, {}, std::move(statsArgs), {});

    ExpressionArguments letArgs;
    letArgs.emplace_back(std::move(expr));
    letArgs.emplace_back(std::move(stats));
    return {"Let"_, {}, std::move(letArgs), {}};
  } else {
    return expr;
  }
}

static ComplexExpression stripRootLetFromExpressionAndFree(ComplexExpression&& expr) {
  if(expr.getHead().getName() == "Let") {
    auto [unused1, unused2, dynamics, unused3] = std::move(expr).decompose();
    auto selectOperatorStates = reinterpret_cast<adaptive::SelectOperatorStates*>(
        get<int64_t>(get<ComplexExpression>(dynamics.at(1)).getDynamicArguments().at(0)));
    delete selectOperatorStates;
    return std::move(get<ComplexExpression>(dynamics.at(0)));
  }
  return std::move(expr);
}

/* Precondition: A single Group is present and is the top level operator */
static ComplexExpression updateTablePositionInSuperAggregateExpr(ComplexExpression&& expr) {
  assert(expr.getHead().getName() == "Group");
  ExpressionArguments outputDynamics;
  auto [head, unused, dynamics, unused_] = std::move(expr).decompose();
  outputDynamics.emplace_back(ComplexExpression("Table"_, {}, {}, {}));
  std::transform(std::make_move_iterator(next(dynamics.begin())),
                 std::make_move_iterator(dynamics.end()), std::back_inserter(outputDynamics),
                 [](auto&& arg) { return std::forward<decltype(arg)>(arg); });
  return {std::move(head), {}, std::move(outputDynamics), {}};
}

/* Precondition: A most one Group is present and, if so, is the top level operator */
static ComplexExpression convertAggregatesToSuperAggregates(ComplexExpression&& expr) {
  if(expr.getHead().getName() != "Group")
    return std::move(expr);
  ExpressionArguments outputDynamics;
  auto [head, unused, dynamics, unused_] = std::move(expr).decompose();
  std::transform(std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
                 std::back_inserter(outputDynamics), [](auto&& arg_) -> ComplexExpression {
                   auto&& arg = get<ComplexExpression>(std::forward<decltype(arg_)>(arg_));
                   if(arg.getHead().getName() == "Count") {
                     auto [unused1, unused2, argDynamics, unused3] = std::move(arg).decompose();
                     return {"Sum"_, {}, std::move(argDynamics), {}};
                   }
                   if(arg.getHead().getName() == "As") {
                     ExpressionArguments outputAsDynamics;
                     auto [asHead, unused1, asDynamics, unused2] = std::move(arg).decompose();
                     assert(asDynamics.size() % 2 == 0);
                     auto it = std::make_move_iterator(asDynamics.begin());
                     while(it != std::make_move_iterator(asDynamics.end())) {
                       outputAsDynamics.push_back(std::move(*it++));
                       if(std::get<ComplexExpression>(*it).getHead().getName() == "Count") {
                         ExpressionArguments aggColumnName;
                         aggColumnName.emplace_back(
                             Symbol(get<Symbol>(outputAsDynamics.back()).getName()));
                         outputAsDynamics.emplace_back(
                             ComplexExpression("Sum"_, {}, std::move(aggColumnName), {}));
                         ++it;
                       } else {
                         outputAsDynamics.push_back(std::move(*it++));
                       }
                     }
                     return {std::move(asHead), {}, std::move(outputAsDynamics), {}};
                   }
                   return std::move(arg);
                 });
  return {std::move(head), {}, std::move(outputDynamics), {}};
}

static ComplexExpression unionTables(ExpressionArguments&& tables) {
  auto it = tables.begin();
  auto result = get<ComplexExpression>(std::move(*it++));
  while(it != tables.end()) {
    auto resultColumnsIt = result.getDynamicArguments().begin();
    auto [unused1_, unused2_, columns, unused3_] =
        get<ComplexExpression>(std::move(*it++)).decompose();
    for(auto&& column : columns) {
      auto&& span = const_cast<ExpressionSpanArgument&&>(std::move(
          get<ComplexExpression>(get<ComplexExpression>(column).getDynamicArguments().at(0))
              .getSpanArguments()
              .at(0)));
      auto& spans = const_cast<ExpressionSpanArguments&>(
          get<ComplexExpression>(
              get<ComplexExpression>(*resultColumnsIt).getDynamicArguments().at(0))
              .getSpanArguments());
      spans.push_back(std::move(span));
      resultColumnsIt++;
    }
  }
  return result;
}

/* Instead of returning the cloned expression, it could instead be inserted as a dynamic arg
 * before the dynamic arg that is being cloned. This would remove the need to update the table
 * position in the super aggregate expression */
static ComplexExpression cloneExprAndMoveTables(const ComplexExpression& e) {
  auto& dynamics = e.getDynamicArguments();
  ExpressionArguments copiedDynamics;
  copiedDynamics.reserve(dynamics.size());
  std::transform(dynamics.begin(), dynamics.end(), std::back_inserter(copiedDynamics),
                 [](auto const& arg) {
                   return std::visit(
                       boss::utilities::overload(
                           [](ComplexExpression const& expr) -> Expression {
                             if(expr.getHead().getName() == "Table") {
                               auto& table = const_cast<ComplexExpression&>(expr);
                               auto [tableHead, unused1_, tableDynamics, unused2_] = std::move(table).decompose();
                               return ComplexExpression("Table"_, {}, std::move(tableDynamics), {});
                             }
                             return cloneExprAndMoveTables(expr);
                           },
                           [](auto const& otherTypes) -> Expression { return otherTypes; }),
                       arg);
                 });
  return {e.getHead(), {}, std::move(copiedDynamics), {}};
}

/* Precondition: There is only a single table in the expression. Could update this to work on a list
 * of tables. */
static ComplexExpression moveSpansToNewTable(ComplexExpression& exprTable, size_t batchNum) {
  auto destDynamics = ExpressionArguments{};
  for(const auto& column : exprTable.getDynamicArguments()) {
    auto const& columnList = get<ComplexExpression>(column).getDynamicArguments().at(0);
    auto&& span = const_cast<ExpressionSpanArgument&&>(
        std::move(get<ComplexExpression>(columnList).getSpanArguments().at(batchNum)));
    ExpressionSpanArguments spans{};
    spans.emplace_back(std::move(span));
    auto destListExpr = ComplexExpression("List"_, {}, {}, std::move(spans));
    auto destColDynamics = ExpressionArguments{};
    destColDynamics.push_back(std::move(destListExpr));
    auto destColExpr = ComplexExpression(Symbol(get<ComplexExpression>(column).getHead().getName()),
                                         {}, std::move(destColDynamics), {});
    destDynamics.push_back(std::move(destColExpr));
  }
  return {"Table"_, {}, std::move(destDynamics), {}};
}

/* Precondition: There is only a single table in the expression. Could update this to return a list
 * of all the tables present. */
static ComplexExpression& getTableReference(ComplexExpression& e, // NOLINT
                                            ComplexExpression& _false) {
  if(e.getHead().getName() == "Table")
    return e;
  auto [head, unused_, dynamics, spans] = std::move(e).decompose();
  for(auto& dynamic : dynamics) {
    if(std::holds_alternative<ComplexExpression>(dynamic)) {
      auto& result = getTableReference(get<ComplexExpression>(dynamic), _false);
      if(result.getHead().getName() == "Table") {
        e = ComplexExpression(std::move(head), {}, std::move(dynamics), std::move(spans));
        return result;
      }
    }
  }
  e = ComplexExpression(std::move(head), {}, std::move(dynamics), std::move(spans));
  return _false;
}

static Expression evaluateDateObject(const ComplexExpression& e) {
  if(std::holds_alternative<std::string>(e.getDynamicArguments().at(0))) {
    auto str = std::get<std::string>(e.getDynamicArguments().at(0));
    std::istringstream iss;
    iss.str(std::string(str));
    struct std::tm tm = {};
    iss >> std::get_time(&tm, "%Y-%m-%d");
    auto t = std::mktime(&tm);
    static int const hoursInADay = 24;
    return (int32_t)(std::chrono::duration_cast<std::chrono::hours>(
                         std::chrono::system_clock::from_time_t(t).time_since_epoch())
                         .count() /
                     hoursInADay);
  } else {
    throw std::runtime_error("DateObject_ does not contain a string");
  }
}

/* Precondition: There is at most one pipeline breaker */
static ComplexExpression generateSubExpressionClone(const ComplexExpression& e) { // NOLINT
  auto& dynamics = e.getDynamicArguments();
  ExpressionArguments copiedDynamics;
  copiedDynamics.reserve(dynamics.size());
  std::for_each(dynamics.begin(), dynamics.end(), [&copiedDynamics](auto& dynamic) {
    if(std::holds_alternative<ComplexExpression>(dynamic)) {
      if(get<ComplexExpression>(dynamic).getHead().getName() == "Table") {
        copiedDynamics.push_back(ComplexExpression("Table"_, {}, {}, {}));
      } else if(get<ComplexExpression>(dynamic).getHead() == "DateObject"_) {
        copiedDynamics.push_back(evaluateDateObject(get<ComplexExpression>(dynamic)));
      } else {
        copiedDynamics.push_back(generateSubExpressionClone(get<ComplexExpression>(dynamic)));
      }
    } else {
      std::visit(
          [&copiedDynamics](auto& value) {
            using T = std::decay_t<decltype(value)>;
            if constexpr(std::is_same_v<T, bool> || std::is_same_v<T, int8_t> ||
                         std::is_same_v<T, int32_t> || std::is_same_v<T, int64_t> ||
                         std::is_same_v<T, float_t> || std::is_same_v<T, double_t> ||
                         std::is_same_v<T, ::std::string> || std::is_same_v<T, Symbol>) {
              copiedDynamics.push_back(value);
            } else
              throw std::runtime_error("Expression contains unknown type");
          },
          dynamic);
    }
  });
  return {e.getHead(), {}, std::move(copiedDynamics), {}};
}

/* Precondition: There is at most one pipeline breaker which can only be a Group which is at the top
 * level. */
static Expression vectorizedEvaluate(ComplexExpression&& expr,
                                     evaluteInternalFunction& pipelineEvaluate) {
  bool pipelineBreakerPresent = expr.getHead().getName() == "Group";
  auto& exprTable = getTableReference(expr);
  if(exprTable == utilities::_false)
    return pipelineEvaluate(std::move(expr));
  auto subExprMaster = generateSubExpressionClone(expr);
#ifdef HAZARD_ADAPTIVE_ENGINE_IN_PIPELINE
#ifdef DEBUG_MODE_VERBOSE
  std::cout << "SubExprMaster before preparing: " << subExprMaster << std::endl;
#endif
#ifdef DEBUG_MODE
  std::cout << "SubExprMaster before preparing: "
            << utilities::injectDebugInfoToSpans(subExprMaster.clone(CloneReason::FOR_TESTING))
            << std::endl;
#endif
  subExprMaster = prepareExpressionForHazardAdaptiveEngine(std::move(subExprMaster));
#ifdef DEBUG_MODE_VERBOSE
  std::cout << "SubExprMaster after preparing:  " << subExprMaster << std::endl;
#endif
#ifdef DEBUG_MODE
  std::cout << "SubExprMaster after preparing:  "
            << utilities::injectDebugInfoToSpans(subExprMaster.clone(CloneReason::FOR_TESTING))
            << std::endl;
#endif
#endif
  auto& subExprMasterTable = getTableReference(subExprMaster);
  auto numBatches =
      get<ComplexExpression>(
          get<ComplexExpression>(exprTable.getDynamicArguments().at(0)).getDynamicArguments().at(0))
          .getSpanArguments()
          .size();
  if(numBatches == 0)
    return pipelineEvaluate(std::move(expr));
#ifdef DEBUG_MODE_VERBOSE
  std::cout << "Expr:               " << expr << std::endl;
  std::cout << "ExprTable:          " << exprTable << std::endl;
  std::cout << "SubExprMaster:      " << subExprMaster << std::endl;
  std::cout << "subExprMasterTable: " << subExprMasterTable << std::endl;
  std::cout << "NumBatches:         " << numBatches << std::endl;
#endif
#ifdef DEBUG_MODE
  std::cout << "Expr:               "
            << utilities::injectDebugInfoToSpans(expr.clone(CloneReason::FOR_TESTING)) << std::endl;
  std::cout << "ExprTable:          "
            << utilities::injectDebugInfoToSpans(exprTable.clone(CloneReason::FOR_TESTING))
            << std::endl;
  std::cout << "SubExprMaster:      "
            << utilities::injectDebugInfoToSpans(subExprMaster.clone(CloneReason::FOR_TESTING))
            << std::endl;
  std::cout << "subExprMasterTable: "
            << utilities::injectDebugInfoToSpans(subExprMasterTable.clone(CloneReason::FOR_TESTING))
            << std::endl;
  std::cout << "NumBatches:         " << numBatches << std::endl;
#endif
  ExpressionArguments results;
  for(size_t batchNum = 0; batchNum < numBatches; batchNum++) {
    subExprMasterTable = moveSpansToNewTable(exprTable, batchNum);
    auto subExpr = cloneExprAndMoveTables(subExprMaster);
#ifdef DEBUG_MODE_VERBOSE
    std::cout << "SubExpr #" << batchNum << ":         " << subExpr << std::endl;
#endif
#ifdef DEBUG_MODE
    std::cout << "SubExpr #" << batchNum << ":         "
              << utilities::injectDebugInfoToSpans(subExpr.clone(CloneReason::FOR_TESTING))
              << std::endl;
#endif
    results.emplace_back(pipelineEvaluate(std::move(subExpr)));
  }
#ifdef DEBUG_MODE_VERBOSE
  auto i = 0;
  for(auto& result : results)
    std::cout << "SubExpr Result #" << i++ << ":  " << result << std::endl;
#endif
#ifdef DEBUG_MODE
  auto i = 0;
  for(auto& result : results)
    std::cout << "SubExpr Result #" << i++ << ":  "
              << utilities::injectDebugInfoToSpans(result.clone(CloneReason::FOR_TESTING))
              << std::endl;
#endif
  auto result = unionTables(std::move(results));
  if(pipelineBreakerPresent) {
    subExprMaster = stripRootLetFromExpressionAndFree(std::move(subExprMaster));
    subExprMaster = updateTablePositionInSuperAggregateExpr(std::move(subExprMaster));
    subExprMaster = convertAggregatesToSuperAggregates(std::move(subExprMaster));
    auto& finalExprTable = getTableReference(subExprMaster);
    finalExprTable = std::move(result);
#ifdef DEBUG_MODE_VERBOSE
    std::cout << "Final expr:         " << subExprMaster << std::endl;
#endif
#ifdef DEBUG_MODE
    std::cout << "Final expr:         "
              << utilities::injectDebugInfoToSpans(subExprMaster.clone(CloneReason::FOR_TESTING))
              << std::endl;
#endif
#if defined(DEBUG_MODE) || defined(DEBUG_MODE_VERBOSE)
    auto finalResult = pipelineEvaluate(std::move(subExprMaster));
#ifdef DEBUG_MODE_VERBOSE
    std::cout << "Final result:       " << finalResult << std::endl;
#else
    std::cout << "Final result:       "
              << utilities::injectDebugInfoToSpans(finalResult.clone(CloneReason::FOR_TESTING))
              << std::endl;
#endif
    return finalResult;
#else
    return pipelineEvaluate(std::move(subExprMaster));
#endif
  }
#if defined(DEBUG_MODE) || defined(DEBUG_MODE_VERBOSE)
#ifdef DEBUG_MODE_VERBOSE
  std::cout << "Final result:       " << result << std::endl;
#else
  std::cout << "Final result:       "
            << utilities::injectDebugInfoToSpans(result.clone(CloneReason::FOR_TESTING))
            << std::endl;
#endif
#endif
  return result;
}

/***************************** BOSS API CONVENIENCE FUNCTIONS *****************************/
static Expression operator|(Expression&& expression, auto&& function) {
  return std::visit(boss::utilities::overload(std::forward<decltype(function)>(function),
                                              [](auto&& atom) -> Expression { return atom; }),
                    std::move(expression));
}

void freeBOSSExpression(BOSSExpression* expression) {
  delete expression; // NOLINT
}
/*****************************************************************************************/

static Expression evaluateInternal(Expression&& e) {
  return std::move(e) | [](ComplexExpression&& e) -> Expression {
    if(e.getHead().getName() != "EvaluateInEngines")
      throw std::runtime_error("Expression does not start with 'EvaluateInEngines'");
    auto [head, unused_, dynamics, spans] = std::move(e).decompose();
    if(spans.size() != 1 || !std::holds_alternative<Span<int64_t>>(spans.at(0)) ||
       std::get<Span<int64_t>>(spans.at(0)).size() == 0)
      throw std::runtime_error("Expected a single int64_t span of pointers to engines in pipeline");
    auto engines = std::vector<evaluteFunction>();
    auto& engineAddresses = get<Span<int64_t>>(spans.at(0));
    std::for_each(engineAddresses.begin(), engineAddresses.end(), [&engines](auto& engineAddress) {
      engines.push_back(reinterpret_cast<evaluteFunction>(engineAddress));
    });
#ifdef FIRST_ENGINE_IS_STORAGE_ENGINE
    auto* r = new BOSSExpression{std::move(get<ComplexExpression>(dynamics.at(0)))};
    auto* oldWrapper = r;
    r = engines[0](r);
    freeBOSSExpression(oldWrapper);
    auto expr = get<ComplexExpression>(std::move(r->delegate));
    freeBOSSExpression(r);
    engines.erase(engines.begin());
#else
    auto& expr = get<ComplexExpression>(dynamics.at(0));
#endif
    evaluteInternalFunction pipelineEvaluate = [&engines](ComplexExpression&& e) -> Expression {
      auto* r = new BOSSExpression{std::move(e)};
      for(auto engine : engines) {
        auto* oldWrapper = r;
        r = engine(r);
        freeBOSSExpression(oldWrapper);
      }
      auto result = std::move(r->delegate);
      freeBOSSExpression(r);
      return result;
    };
    return vectorizedEvaluate(std::move(expr), pipelineEvaluate);
  };
}

static Expression evaluate(Expression&& expr) {
#ifdef DEBUG_MODE_VERBOSE
  std::cout << "Coordinator input:  " << expr << std::endl;
#endif
#ifdef DEBUG_MODE
  std::cout << "Coordinator input:  "
            << utilities::injectDebugInfoToSpans(expr.clone(CloneReason::FOR_TESTING)) << std::endl;
#endif
  try {
    return evaluateInternal(std::move(expr));
  } catch(std::exception const& e) {
    ExpressionArguments args;
    args.reserve(2);
    args.emplace_back(std::move(expr));
    args.emplace_back(std::string{e.what()});
    return ComplexExpression{"ErrorWhenEvaluatingExpression"_, std::move(args)};
  }
}

extern "C" __attribute__((visibility("default"))) BOSSExpression* evaluate(BOSSExpression* e) {
  return new BOSSExpression{.delegate = evaluate(std::move(e->delegate))};
}