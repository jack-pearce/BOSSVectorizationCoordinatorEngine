#include <BOSS.hpp>
#include <Expression.hpp>
#include <ExpressionUtilities.hpp>
#include <Utilities.hpp>
#include <algorithm>
#include <chrono>
#include <iomanip>
#include <iostream>
#include <optional>

#include "/home/jcp122/repos/BOSSHazardAdaptiveEngine/Source/utilities/sharedDataTypes.hpp"
// #include "/repos/BOSSHazardAdaptiveEngine/Source/utilities/sharedDataTypes.hpp"
#include "config.hpp"
#include "memoryPool.hpp"

// #define DEBUG_MULTI_THREAD
// #define DEBUG_MODE
// #define DEBUG_MODE_VERBOSE
// #define DEBUG_JOIN_SPECIFIC
// #define DEBUG_EXPR_SENT_TO_LAST_ENGINE

#define FIRST_ENGINE_IS_STORAGE_ENGINE
#define HAZARD_ADAPTIVE_ENGINE_IN_PIPELINE
// #define EVALUATE_NON_PARTITIONED_JOINS_IN_VELOX

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

using adaptive::SelectOperatorStates;

using vectorization::config::minBuildSideTableLengthForPartitionedHashJoin;

namespace utilities {
auto _false = ComplexExpression("False"_, {}, {}, {});
}

static ComplexExpression& getTableOrJoinReference(ComplexExpression& e,
                                                  ComplexExpression& _false = utilities::_false);

#if defined(DEBUG_MODE) || defined(DEBUG_JOIN_SPECIFIC) || defined(DEBUG_EXPR_SENT_TO_LAST_ENGINE)
namespace utilities {
static boss::Expression injectDebugInfoToSpansNumSpans(boss::Expression&& expr) {
  return std::visit(
      boss::utilities::overload(
          [&](boss::ComplexExpression&& e) -> boss::Expression {
            auto [head, unused_, dynamics, spans] = std::move(e).decompose();
            boss::ExpressionArguments debugDynamics;
            debugDynamics.reserve(dynamics.size() + spans.size());
            std::transform(
                std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
                std::back_inserter(debugDynamics), [](auto&& arg) {
                  return injectDebugInfoToSpansNumSpans(std::forward<decltype(arg)>(arg));
                });
            auto numSpans = spans.size();
            if(numSpans > 0) {
              auto totalRows = std::accumulate(
                  spans.begin(), spans.end(), (size_t)0, [](auto total, auto&& span) {
                    return total +
                           std::visit([](auto&& typedSpan) -> size_t { return typedSpan.size(); },
                                      std::forward<decltype(span)>(span));
                  });
              debugDynamics.emplace_back("Spans"_((int64_t)numSpans, (int64_t)totalRows));
            }
            return boss::ComplexExpression(std::move(head), {}, std::move(debugDynamics), {});
          },
          [](auto&& otherTypes) -> boss::Expression { return otherTypes; }),
      std::move(expr));
}

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

static boss::ComplexExpression shallowCopy(boss::ComplexExpression const& e) {
  auto const& head = e.getHead();
  auto const& dynamics = e.getDynamicArguments();
  auto const& spans = e.getSpanArguments();
  boss::ExpressionArguments dynamicsCopy;
  dynamicsCopy.reserve(dynamics.size());
  std::transform(dynamics.begin(), dynamics.end(), std::back_inserter(dynamicsCopy),
                 [](auto const& arg) {
                   return std::visit(
                       boss::utilities::overload(
                           [&](boss::ComplexExpression const& expr) -> boss::Expression {
                             return shallowCopy(expr);
                           },
                           [](auto const& otherTypes) -> boss::Expression { return otherTypes; }),
                       arg);
                 });
  boss::expressions::ExpressionSpanArguments spansCopy;
  spansCopy.reserve(spans.size());
  std::transform(spans.begin(), spans.end(), std::back_inserter(spansCopy), [](auto const& span) {
    return std::visit(
        [](auto const& typedSpan) -> boss::expressions::ExpressionSpanArgument {
          // just do a shallow copy of the span
          // the storage's span keeps the ownership
          // (since the storage will be alive until the query finishes)
          using SpanType = std::decay_t<decltype(typedSpan)>;
          using T = std::remove_const_t<typename SpanType::element_type>;
          if constexpr(std::is_same_v<T, bool>) {
            return SpanType(typedSpan.begin(), typedSpan.size(), []() {});
          } else {
            // force non-const value for now (otherwise expressions cannot be moved)
            auto* ptr = const_cast<T*>(typedSpan.begin()); // NOLINT
            return boss::Span<T>(ptr, typedSpan.size(), []() {});
          }
        },
        span);
  });
  return {head, {}, std::move(dynamicsCopy), std::move(spansCopy)};
}

static ComplexExpression addIdToPredicatesAux(ComplexExpression&& expr, int& predicateCount) {
  auto [head, unused, dynamics, unused_] = std::move(expr).decompose();
  ExpressionArguments outputDynamics;
  outputDynamics.reserve(dynamics.size());
  std::transform(std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
                 std::back_inserter(outputDynamics),
                 [&predicateCount](auto&& arg_) -> ComplexExpression {
                   auto&& arg = get<ComplexExpression>(std::forward<decltype(arg_)>(arg_));
                   if(arg.getHead().getName() == "And") {
                     return addIdToPredicatesAux(std::move(arg), predicateCount);
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
static ComplexExpression addIdToPredicates(ComplexExpression&& expr, int& predicateCount) {
  auto [head, unused, dynamics, unused_] = std::move(expr).decompose();
  ExpressionArguments outputDynamics;
  outputDynamics.reserve(dynamics.size());
  std::transform(std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
                 std::back_inserter(outputDynamics), [&predicateCount](auto&& arg_) -> Expression {
                   if(std::holds_alternative<ComplexExpression>(arg_)) {
                     auto&& arg = get<ComplexExpression>(std::forward<decltype(arg_)>(arg_));
                     if(arg.getHead().getName() == "Where") {
                       return addIdToPredicatesAux(std::move(arg), predicateCount);
                     }
                     return addIdToPredicates(std::move(arg), predicateCount);
                   } else {
                     return arg_;
                   }
                 });
  return {std::move(head), {}, std::move(outputDynamics), {}};
}

static ComplexExpression addParallelInformation(ComplexExpression&& expr, int vectorizedDOP) {
  auto letArgs = ExpressionArguments(std::move(expr));
  letArgs.emplace_back(ComplexExpression("Parallel"_, {}, ExpressionArguments(vectorizedDOP), {}));
  return {"Let"_, {}, std::move(letArgs), {}};
}

static ComplexExpression addStatsInformation(ComplexExpression&& expr,
                                             SelectOperatorStates* statesPtr) {
  auto letArgs = ExpressionArguments(std::move(expr));
  letArgs.emplace_back(ComplexExpression(
      "Stats"_, {}, ExpressionArguments(reinterpret_cast<int64_t>(statesPtr)), {}));
  return {"Let"_, {}, std::move(letArgs), {}};
}

class StatsRaiiWrapper {
public:
  explicit StatsRaiiWrapper(int predicateCount)
      : selectOperatorStates(std::make_unique<SelectOperatorStates>(predicateCount)) {}
  [[nodiscard]] SelectOperatorStates* getStates() const { return selectOperatorStates.get(); }
  StatsRaiiWrapper(const StatsRaiiWrapper&) = delete;
  StatsRaiiWrapper& operator=(const StatsRaiiWrapper&) = delete;

private:
  std::unique_ptr<SelectOperatorStates> selectOperatorStates;
};

static ComplexExpression unionTables(ExpressionArguments&& tables) {
  auto it = tables.begin();
  auto result = get<ComplexExpression>(std::move(*it++));
  while(it != tables.end()) {
    auto resultColumnsIt = result.getDynamicArguments().begin();
    auto [unused1_, unused2_, columns, unused3_] =
        get<ComplexExpression>(std::move(*it++)).decompose();
    for(auto&& column : columns) {
      auto& spans = const_cast<ExpressionSpanArguments&>(
          get<ComplexExpression>(
              get<ComplexExpression>(*resultColumnsIt).getDynamicArguments().at(0))
              .getSpanArguments());
      auto numSpans =
          get<ComplexExpression>(get<ComplexExpression>(column).getDynamicArguments().at(0))
              .getSpanArguments()
              .size();
      for(size_t i = 0; i < numSpans; ++i) {
        auto&& span = const_cast<ExpressionSpanArgument&&>(std::move(
            get<ComplexExpression>(get<ComplexExpression>(column).getDynamicArguments().at(0))
                .getSpanArguments()
                .at(i)));
        spans.push_back(std::move(span));
      }
      resultColumnsIt++;
    }
  }
  return result;
}

/* Instead of returning the cloned expression, it could instead be inserted as a dynamic arg
 * before the dynamic arg that is being cloned. This would remove the need to update the table
 * position in the super aggregate expression */
static ComplexExpression cloneExprAndMoveTables(const ComplexExpression& e) {
  if(e.getHead().getName() == "Table" || e.getHead().getName() == "TableIndexed" ||
     e.getHead().getName() == "Join") {
    return std::move(const_cast<ComplexExpression&>(e));
  }
  auto& dynamics = e.getDynamicArguments();
  ExpressionArguments copiedDynamics;
  copiedDynamics.reserve(dynamics.size());
  std::transform(
      dynamics.begin(), dynamics.end(), std::back_inserter(copiedDynamics), [](auto const& arg) {
        return std::visit(boss::utilities::overload(
                              [](ComplexExpression const& expr) -> Expression {
                                return cloneExprAndMoveTables(expr);
                              },
                              [](auto const& otherTypes) -> Expression { return otherTypes; }),
                          arg);
      });
  return {e.getHead(), {}, std::move(copiedDynamics), {}};
}

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

static ComplexExpression moveSpansToNewTableOrJoin(ComplexExpression& exprTable, size_t batchNum) {
  if(exprTable.getHead().getName() == "Table") {
    return moveSpansToNewTable(exprTable, batchNum);
  } else if(exprTable.getHead().getName() == "TableIndexed") {
    auto dynamics = ExpressionArguments{};
    dynamics.emplace_back(shallowCopy(get<ComplexExpression>(exprTable.getArguments().at(0))));
    auto&& span1 = const_cast<ExpressionSpanArgument&&>(std::move(
        get<ComplexExpression>(exprTable.getArguments().at(1)).getSpanArguments().at(batchNum)));
    ExpressionSpanArguments spans1{};
    spans1.emplace_back(std::move(span1));
    dynamics.emplace_back(ComplexExpression("Indexes"_, {}, {}, std::move(spans1)));
    dynamics.emplace_back(shallowCopy(get<ComplexExpression>(exprTable.getArguments().at(2))));
    auto&& span2 = const_cast<ExpressionSpanArgument&&>(std::move(
        get<ComplexExpression>(exprTable.getArguments().at(3)).getSpanArguments().at(batchNum)));
    ExpressionSpanArguments spans2{};
    spans2.emplace_back(std::move(span2));
    dynamics.emplace_back(ComplexExpression("Indexes"_, {}, {}, std::move(spans2)));
    return {"TableIndexed"_, {}, std::move(dynamics), {}};
  } else { // "Join"_
    auto destDynamics = ExpressionArguments{};
#ifdef HAZARD_ADAPTIVE_ENGINE_IN_PIPELINE
    auto shallowCopyTableAndMovePartition = [](ComplexExpression& radixPartitionExpr,
                                               size_t batchNum) -> ComplexExpression {
      auto dynamics = ExpressionArguments{};
      dynamics.emplace_back(
          shallowCopy(get<ComplexExpression>(radixPartitionExpr.getArguments().at(0))));
      dynamics.emplace_back(radixPartitionExpr.getArguments().at(1 + batchNum));
      return {"RadixPartition"_, {}, std::move(dynamics), {}};
    };
    destDynamics.emplace_back(shallowCopyTableAndMovePartition(
        get<ComplexExpression>(exprTable.getArguments().at(0)), batchNum));
    destDynamics.emplace_back(shallowCopyTableAndMovePartition(
        get<ComplexExpression>(exprTable.getArguments().at(1)), batchNum));
#else
    destDynamics.emplace_back(
        moveSpansToNewTable(get<ComplexExpression>(exprTable.getArguments().at(0)), batchNum));
    destDynamics.emplace_back(
        moveSpansToNewTable(get<ComplexExpression>(exprTable.getArguments().at(1)), batchNum));
#endif
    destDynamics.emplace_back(get<ComplexExpression>(exprTable.getArguments().at(2))
                                  .clone(CloneReason::EVALUATE_CONST_EXPRESSION));
    return {"Join"_, {}, std::move(destDynamics), {}};
  }
}

static ComplexExpression& getTableOrJoinReference(ComplexExpression& e, ComplexExpression& _false) {
  if(e.getHead().getName() == "Table" || e.getHead().getName() == "TableIndexed" ||
     e.getHead().getName() == "Join")
    return e;
  auto [head, unused_, dynamics, spans] = std::move(e).decompose();
  for(auto& dynamic : dynamics) {
    if(std::holds_alternative<ComplexExpression>(dynamic)) {
      auto& result = getTableOrJoinReference(get<ComplexExpression>(dynamic), _false);
      if(result.getHead().getName() == "Table" || result.getHead().getName() == "TableIndexed" ||
         result.getHead().getName() == "Join") {
        e = ComplexExpression(std::move(head), {}, std::move(dynamics), std::move(spans));
        return result;
      }
    }
  }
  e = ComplexExpression(std::move(head), {}, std::move(dynamics), std::move(spans));
  return _false;
}

static int getNumBatchesInTableOrJoinReference(ComplexExpression& e) {
  if(e.getHead().getName() == "Table") {
    return static_cast<int>(
        get<ComplexExpression>(
            get<ComplexExpression>(e.getDynamicArguments().at(0)).getDynamicArguments().at(0))
            .getSpanArguments()
            .size());
  }
  if(e.getHead().getName() == "TableIndexed") {
    return static_cast<int>(
        get<ComplexExpression>(e.getDynamicArguments().at(1)).getSpanArguments().size());
  }
  return static_cast<int>(
             get<ComplexExpression>(e.getDynamicArguments().at(0)).getArguments().size()) -
         1;
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
      } else if(get<ComplexExpression>(dynamic).getHead().getName() == "TableIndexed") {
        copiedDynamics.push_back(ComplexExpression("TableIndexed"_, {}, {}, {}));
      } else if(get<ComplexExpression>(dynamic).getHead().getName() == "Join") {
        copiedDynamics.push_back(ComplexExpression("Join"_, {}, {}, {}));
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

/* Precondition: There is at most one pipeline breaker which can only be a Group or Top which is at
 * the top level. */
static void vectorizedEvaluateSingleThread(const ComplexExpression& expr,
                                           ComplexExpression& exprTable,
                                           evaluteInternalFunction& evaluateFunc, int startBatch,
                                           int numBatches, int vectorizedDOP,
                                           ExpressionArguments& outputVector, int outputIndex,
                                           bool hazardAdaptiveEngineInPipeline) {
  auto subExprMaster = generateSubExpressionClone(expr);
#ifdef HAZARD_ADAPTIVE_ENGINE_IN_PIPELINE
  auto stats = std::optional<StatsRaiiWrapper>(std::nullopt);
  if(hazardAdaptiveEngineInPipeline) {
#ifdef DEBUG_MODE_VERBOSE
    std::cout << "SubExprMaster before preparing: " << subExprMaster << std::endl;
#endif
#ifdef DEBUG_MODE
    std::cout << "SubExprMaster before preparing: "
              << utilities::injectDebugInfoToSpans(subExprMaster.clone(CloneReason::FOR_TESTING))
              << std::endl;
#endif
    subExprMaster = addParallelInformation(std::move(subExprMaster), vectorizedDOP);
    int predicateCount = 0;
    subExprMaster = addIdToPredicates(std::move(subExprMaster), predicateCount);
#if defined(DEBUG_MODE) || defined(DEBUG_MODE_VERBOSE)
    std::cout << "Identified " << predicateCount << " predicates" << std::endl;
#endif
    if(predicateCount > 0) {
      stats.emplace(predicateCount);
      subExprMaster = addStatsInformation(std::move(subExprMaster), stats.value().getStates());
    }
#ifdef DEBUG_MODE_VERBOSE
    std::cout << "SubExprMaster after preparing:  " << subExprMaster << std::endl;
#endif
#ifdef DEBUG_MODE
    std::cout << "SubExprMaster after preparing:  "
              << utilities::injectDebugInfoToSpans(subExprMaster.clone(CloneReason::FOR_TESTING))
              << std::endl;
#endif
  }
#endif
  auto& subExprMasterTable = getTableOrJoinReference(subExprMaster);
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
  for(int batchNum = startBatch; batchNum < startBatch + numBatches; ++batchNum) {
    // Move batchNum'th span into the subExprMasterTable within subExprMaster
    subExprMasterTable = moveSpansToNewTableOrJoin(exprTable, batchNum);
    // clone the master expression and move the tables into a new expression to evaluate
    auto subExpr = cloneExprAndMoveTables(subExprMaster);
#ifdef DEBUG_MODE_VERBOSE
    std::cout << "SubExpr #" << batchNum << ":         " << subExpr << std::endl;
#endif
#ifdef DEBUG_MODE
    std::cout << "SubExpr #" << batchNum << ":         "
              << utilities::injectDebugInfoToSpans(subExpr.clone(CloneReason::FOR_TESTING))
              << std::endl;
#endif
    results.emplace_back(evaluateFunc(std::move(subExpr)));
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
#if defined(DEBUG_MODE) || defined(DEBUG_MODE_VERBOSE)
#ifdef DEBUG_MODE_VERBOSE
  std::cout << "Final result:       " << result << std::endl;
#else
  std::cout << "Final result:       "
            << utilities::injectDebugInfoToSpans(result.clone(CloneReason::FOR_TESTING))
            << std::endl;
#endif
#endif
  outputVector[outputIndex] = std::move(result);
}

static Expression vectorizedEvaluate(ComplexExpression&& e, evaluteInternalFunction& evaluateFunc,
                                     bool hazardAdaptiveEngineInPipeline) {
  auto expr = std::move(e);
  auto& exprTable = getTableOrJoinReference(expr);
  if(exprTable == utilities::_false)
    return evaluateFunc(std::move(expr));
  auto numBatches = getNumBatchesInTableOrJoinReference(exprTable);
#ifdef DEBUG_MULTI_THREAD
  std::cout << "Number of batches: " << numBatches << std::endl;
#endif
  if(numBatches == 0) {
    if(exprTable.getHead().getName() == "Table") {
      return std::move(exprTable);
    }
    if(exprTable.getHead().getName() == "TableIndexed") {
      return evaluateFunc(std::move(expr));
    }
    return "Table"_();
  }

  int dop = std::min(numBatches, vectorization::config::maxVectorizedDOP);
  ExpressionArguments results;
  results.resize(dop);
#ifdef DEBUG_MULTI_THREAD
  std::cout << "Using " << dop << " degrees of parallelism" << std::endl;
#endif
  if(dop == 1) {
    vectorizedEvaluateSingleThread(expr, exprTable, evaluateFunc, 0, numBatches, 1, results, 0,
                                   hazardAdaptiveEngineInPipeline);
  } else {
    auto& pool = ThreadPool::getInstance();

    int baselineBatchesPerThread = numBatches / dop;
    int remainingBatches = numBatches % dop;
    int startBatchNum = 0;
    int batchesPerThread;
    auto& synchroniser = Synchroniser::getInstance();
    for(auto i = 0; i < dop; ++i) {
      if(i < dop - 1) {
        batchesPerThread = baselineBatchesPerThread + (i < remainingBatches);
      } else {
        batchesPerThread = numBatches - startBatchNum;
      }
#ifdef DEBUG_MULTI_THREAD
      std::cout << "Thread " << i << " processing " << batchesPerThread
                << " batches starting from batch " << startBatchNum << std::endl;
#endif
      pool.enqueue([&synchroniser, &expr, &exprTable, &evaluateFunc, startBatchNum,
                    batchesPerThread, dop, &results, i, hazardAdaptiveEngineInPipeline]() {
        vectorizedEvaluateSingleThread(expr, exprTable, evaluateFunc, startBatchNum,
                                       batchesPerThread, dop, results, i,
                                       hazardAdaptiveEngineInPipeline);
        synchroniser.taskComplete();
      });
      startBatchNum += batchesPerThread;
    }
    synchroniser.waitUntilComplete(dop);
  }
  auto result = unionTables(std::move(results));
#ifdef DEBUG_MODE_VERBOSE
  std::cout << "Combined result:    " << result << std::endl;
#endif
#ifdef DEBUG_MODE
  std::cout << "Combined result:    "
            << utilities::injectDebugInfoToSpans(result.clone(CloneReason::FOR_TESTING))
            << std::endl;
#endif

  return result;
}

template <typename T> inline int getLengthOfSpans(const ExpressionSpanArguments& spans) {
  int n = 0;
  for(auto& untypedSpan : spans) {
    auto& span = std::get<Span<T>>(untypedSpan);
    n += span.size();
  }
#ifdef DEBUG_JOIN_SPECIFIC
  std::cout << "Join input table length on build side: " << n << std::endl;
#endif
  return n;
}

bool partitionedJoinRequired(const ComplexExpression& expr) {
  const ComplexExpression& buildSide = get<ComplexExpression>(expr.getDynamicArguments()[0]);
  const ComplexExpression& table = get<ComplexExpression>(buildSide.getDynamicArguments()[0]);
  const ExpressionSpanArguments& spans =
      get<ComplexExpression>(table.getArguments().at(0)).getSpanArguments();
  int n = std::visit(
      [&spans]<typename T>(const Span<T>& /*span*/) { return getLengthOfSpans<T>(spans); },
      spans[0]);
  return n > minBuildSideTableLengthForPartitionedHashJoin;
}

static Expression batchEvaluate(ComplexExpression&& expr, evaluteInternalFunction& evaluateFunc) {
  expr = addParallelInformation(std::move(expr), vectorization::config::maxVectorizedDOP);
#ifdef DEBUG_MODE_VERBOSE
  std::cout << "Running batch evaluate of: " << expr << std::endl;
#endif
#if defined(DEBUG_MODE) || defined(DEBUG_JOIN_SPECIFIC)
  std::cout << "Running batch evaluate of: "
            << utilities::injectDebugInfoToSpansNumSpans(expr.clone(CloneReason::FOR_TESTING))
            << std::endl;
#endif
  return evaluateFunc(std::move(expr));
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

static Expression evaluateDispatcher(Expression&& e, evaluteInternalFunction& wholePipelineEvaluate,
                                     evaluteInternalFunction& firstEngineEvaluate,
                                     evaluteInternalFunction& pipelineEvaluateExceptFirstEngine) {
  if(std::holds_alternative<ComplexExpression>(e) &&
     get<ComplexExpression>(e).getHead().getName() != "Table") { // Need to evaluate, perform DFS
    auto [head, unused_, dynamics, spans] = get<ComplexExpression>(std::move(e)).decompose();
    ExpressionArguments evaluatedDynamics;
    evaluatedDynamics.reserve(dynamics.size());
    // Special case for Join: Double evaluate branches (1st to evaluate any pipeline
    // breakers, 2nd to evaluate any remaining expression)
    if(head.getName() == "Join") {
      int index = 0;
      std::transform(
          std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
          std::back_inserter(evaluatedDynamics), [&](auto&& arg) {
            if(index++ >= 2) {
              return std::forward<decltype(arg)>(arg); // Predicate
            }
            if(get<ComplexExpression>(arg).getHead().getName() == "Table") {
              return std::forward<decltype(arg)>(arg); // Nothing to evaluate
            }
            auto evaluatedArg = evaluateDispatcher( // Evaluate any pipeline breakers if present
                std::forward<decltype(arg)>(arg), wholePipelineEvaluate, firstEngineEvaluate,
                pipelineEvaluateExceptFirstEngine);
            if(get<ComplexExpression>(evaluatedArg).getHead().getName() == "Table") {
              return std::move(evaluatedArg); // Nothing to evaluate
            }
            return vectorizedEvaluate(std::move(get<ComplexExpression>(evaluatedArg)),
                                      wholePipelineEvaluate, true);
          });
      // Special case for Group, Top, Order: Double evaluate table expr (1st to evaluate any
      // pipeline breakers, 2nd to evaluate any remaining expression)
    } else if(head.getName() == "Group" || head.getName() == "Top" || head.getName() == "Order") {
      int index = 0;
      std::transform(
          std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
          std::back_inserter(evaluatedDynamics), [&](auto&& arg) {
            if(index++ >= 1) {
              return std::forward<decltype(arg)>(arg); // By and As args etc.
            }
            if(get<ComplexExpression>(arg).getHead().getName() == "Table") {
              return std::forward<decltype(arg)>(arg); // Nothing to evaluate
            }
            auto evaluatedArg = evaluateDispatcher( // Evaluate any pipeline breakers if present
                std::forward<decltype(arg)>(arg), wholePipelineEvaluate, firstEngineEvaluate,
                pipelineEvaluateExceptFirstEngine);
            if(get<ComplexExpression>(evaluatedArg).getHead().getName() == "Table") {
              return std::move(evaluatedArg); // Nothing to evaluate
            }
            return vectorizedEvaluate(std::move(get<ComplexExpression>(evaluatedArg)),
                                      wholePipelineEvaluate, true);
          });
    } else { // Continue DFS as normal
      std::transform(
          std::make_move_iterator(dynamics.begin()), std::make_move_iterator(dynamics.end()),
          std::back_inserter(evaluatedDynamics), [&](auto&& arg) {
            return evaluateDispatcher(std::forward<decltype(arg)>(arg), wholePipelineEvaluate,
                                      firstEngineEvaluate, pipelineEvaluateExceptFirstEngine);
          });
    }
    auto unevaluated =
        ComplexExpression(std::move(head), {}, std::move(evaluatedDynamics), std::move(spans));
    if(unevaluated.getHead().getName() == "Join") { // Pipeline breaker
#ifdef DEBUG_JOIN_SPECIFIC
      std::cout << "Join: "
                << utilities::injectDebugInfoToSpansNumSpans(
                       unevaluated.clone(CloneReason::FOR_TESTING))
                << std::endl;
      std::cout << "Partition " << (partitionedJoinRequired(unevaluated) ? "IS" : "IS NOT")
                << " required" << std::endl;
#endif
      if(partitionedJoinRequired(unevaluated)) {
        auto [head, unused_, dynamics, spans] = std::move(unevaluated).decompose();
        unevaluated =
            ComplexExpression(Symbol("PartitionedJoin"), {}, std::move(dynamics), std::move(spans));
        auto result =
            get<ComplexExpression>(batchEvaluate(std::move(unevaluated), firstEngineEvaluate));
        if(result.getHead().getName() == "Join") {
          return std::move(result);
        } else { // Could not evaluate in hazardAdaptiveLib (e.g. multi-key Join), evaluate in Velox
          auto [head, unused_, dynamics, spans] = std::move(result).decompose();
          unevaluated =
              ComplexExpression(Symbol("Join"), {}, std::move(dynamics), std::move(spans));
          return batchEvaluate(std::move(unevaluated), pipelineEvaluateExceptFirstEngine);
        }
      }
#ifdef EVALUATE_NON_PARTITIONED_JOINS_IN_VELOX // Batch evaluate in Velox
      return batchEvaluate(std::move(unevaluated), pipelineEvaluateExceptFirstEngine);
#else // Batch evaluate in hazard adaptive engine
      auto result =
          get<ComplexExpression>(batchEvaluate(std::move(unevaluated), firstEngineEvaluate));
      if(result.getHead().getName() == "Join") { // Hazard adaptive engine failed to evaluate
        return batchEvaluate(std::move(unevaluated), pipelineEvaluateExceptFirstEngine);
      }
      return std::move(result);
#endif
    } else if(unevaluated.getHead().getName() == "Group") { // Pipeline breaker
      return batchEvaluate(std::move(unevaluated), firstEngineEvaluate);
    } else if(unevaluated.getHead().getName() == "Top" ||
              unevaluated.getHead().getName() == "Order") { // Pipeline breaker
      return batchEvaluate(std::move(unevaluated), pipelineEvaluateExceptFirstEngine);
    }
    return std::move(unevaluated);
  }
  return std::move(e); // Nothing to evaluate
}

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

    evaluteInternalFunction wholePipelineEvaluate =
        [&engines](ComplexExpression&& e) -> Expression {
      auto* r = new BOSSExpression{std::move(e)};
#ifdef DEBUG_EXPR_SENT_TO_LAST_ENGINE
      size_t index = 0;
      size_t totalEngines = engines.size();
      for(auto engine : engines) {
        auto* oldWrapper = r;
        if(index++ == totalEngines - 1) {
          Expression expr = std::move(r->delegate);
          std::cout << "Last engine input expression: "
                    << utilities::injectDebugInfoToSpansNumSpans(
                           expr.clone(CloneReason::FOR_TESTING))
                    << '\n'
                    << std::endl;
          r = new BOSSExpression{std::move(expr)};
        }
        r = engine(r);
        freeBOSSExpression(oldWrapper);
      }
#else
      for(auto engine : engines) {
        auto* oldWrapper = r;
        r = engine(r);
        freeBOSSExpression(oldWrapper);
      }
#endif
      auto result = std::move(r->delegate);
      freeBOSSExpression(r);
      return result;
    };

    evaluteInternalFunction firstEngineEvaluate = [&engines](ComplexExpression&& e) -> Expression {
      auto* r = new BOSSExpression{std::move(e)};
      auto* oldWrapper = r;
      r = engines[0](r);
      freeBOSSExpression(oldWrapper);
      auto result = std::move(r->delegate);
      freeBOSSExpression(r);
      return result;
    };

    evaluteInternalFunction pipelineEvaluateExceptFirstEngine =
        [&engines](ComplexExpression&& e) -> Expression {
      auto* r = new BOSSExpression{std::move(e)};
      auto engineIterator = std::next(engines.begin());
      for(; engineIterator != engines.end(); ++engineIterator) {
        auto* oldWrapper = r;
#ifdef DEBUG_EXPR_SENT_TO_LAST_ENGINE
        if(engineIterator == std::prev(engines.end())) {
          Expression expr = std::move(r->delegate);
          std::cout << "Last engine input expression: "
                    << utilities::injectDebugInfoToSpansNumSpans(
                           expr.clone(CloneReason::FOR_TESTING))
                    << '\n'
                    << std::endl;
          r = new BOSSExpression{std::move(expr)};
        }

#endif
        r = (*engineIterator)(r);
        freeBOSSExpression(oldWrapper);
      }
      auto result = std::move(r->delegate);
      freeBOSSExpression(r);
      return result;
    };

    bool finalEvaluateRequired =
        !(expr.getHead().getName() == "Group" || expr.getHead().getName() == "Top" ||
          expr.getHead().getName() == "Order");
    auto result = get<ComplexExpression>(evaluateDispatcher(std::move(expr), wholePipelineEvaluate,
                                                            firstEngineEvaluate,
                                                            pipelineEvaluateExceptFirstEngine));
#ifdef DEBUG_MODE_VERBOSE
    std::cout << "Result after all pipeline breakers evaluated: " << result << std::endl;
#endif
#ifdef DEBUG_MODE
    std::cout << "Result after all pipeline breakers evaluated: "
              << utilities::injectDebugInfoToSpans(result.clone(CloneReason::FOR_TESTING))
              << std::endl;
#endif

    if(!finalEvaluateRequired) { // Final evaluation not required if root was a Group, Top, or Order
      return result;
    }
    return vectorizedEvaluate(std::move(result), wholePipelineEvaluate, true);
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