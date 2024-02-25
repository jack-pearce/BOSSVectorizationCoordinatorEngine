#define CATCH_CONFIG_RUNNER
#include "../Source/BOSS.hpp"
#include "../Source/BootstrapEngine.hpp"
#include "../Source/ExpressionUtilities.hpp"
#include <catch2/catch.hpp>
#include <numeric>
#include <variant>

using boss::Expression;
using std::string;
using std::literals::string_literals::operator""s;
using boss::utilities::operator""_;
using Catch::Generators::random;
using Catch::Generators::table;
using Catch::Generators::take;
using Catch::Generators::values;
using std::vector;
using namespace Catch::Matchers;
using boss::expressions::CloneReason;
using boss::expressions::generic::get;
using boss::expressions::generic::get_if;
using boss::expressions::generic::holds_alternative;
namespace boss {
using boss::expressions::atoms::Span;
};
using std::int32_t;
using std::int64_t;

static std::vector<string>
    librariesToTest{}; // NOLINT(cppcoreguidelines-avoid-non-const-global-variables)

using intType = int32_t;
using floatType = double;

auto createTwoSpansIntStartingFrom = [](intType n) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<intType> v1 = {0 + n, 1 + n};
  std::vector<intType> v2 = {2 + n, 3 + n};
  auto s1 = boss::Span<intType>(std::move(v1));
  auto s2 = boss::Span<intType>(std::move(v2));
  SpanArguments args;
  args.emplace_back(std::move(s1));
  args.emplace_back(std::move(s2));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

auto createFourSpansIntStartingFrom = [](intType n) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<intType> v1 = {0 + n, 4 + n};
  std::vector<intType> v2 = {1 + n, 5 + n};
  std::vector<intType> v3 = {2 + n, 6 + n};
  std::vector<intType> v4 = {0 + n, 4 + n};
  auto s1 = boss::Span<intType>(std::move(v1));
  auto s2 = boss::Span<intType>(std::move(v2));
  auto s3 = boss::Span<intType>(std::move(v3));
  auto s4 = boss::Span<intType>(std::move(v4));
  SpanArguments args;
  args.emplace_back(std::move(s1));
  args.emplace_back(std::move(s2));
  args.emplace_back(std::move(s3));
  args.emplace_back(std::move(s4));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

auto createTwoTwoNumIntSpans = [](intType a, intType b, intType c, intType d) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<intType> v1 = {a, b};
  std::vector<intType> v2 = {c, d};
  auto s1 = boss::Span<intType>(std::move(v1));
  auto s2 = boss::Span<intType>(std::move(v2));
  SpanArguments args;
  args.emplace_back(std::move(s1));
  args.emplace_back(std::move(s2));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

auto createTwoTwoNumFloatSpans = [](floatType a, floatType b, floatType c, floatType d) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<floatType> v1 = {a, b};
  std::vector<floatType> v2 = {c, d};
  auto s1 = boss::Span<floatType>(std::move(v1));
  auto s2 = boss::Span<floatType>(std::move(v2));
  SpanArguments args;
  args.emplace_back(std::move(s1));
  args.emplace_back(std::move(s2));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

auto createTwoTwoStrStringSpans = [](std::string a, std::string b, std::string c, std::string d) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<std::string> v1 = {a, b};
  std::vector<std::string> v2 = {c, d};
  auto s1 = boss::Span<std::string>(std::move(v1));
  auto s2 = boss::Span<std::string>(std::move(v2));
  SpanArguments args;
  args.emplace_back(std::move(s1));
  args.emplace_back(std::move(s2));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

TEST_CASE("Delegate bootstrapping - simple", "[vectorization-engine]") {
  auto engine = boss::engines::BootstrapEngine();
  REQUIRE(librariesToTest.size() >= 2);
  boss::ExpressionArguments libsArg;
  for(auto it = librariesToTest.begin() + 1; it != librariesToTest.end(); ++it)
    libsArg.emplace_back(*it);
  auto libsExpr = boss::ComplexExpression("List"_, std::move(libsArg));
  auto eval = [&](boss::Expression&& expr) mutable {
    return engine.evaluate(
        "DelegateBootstrapping"_(librariesToTest[0], std::move(libsExpr), std::move(expr)));
  };

  auto res = eval("Plus"_(1, 2));
  CHECK(res == 3); // NOLINT
}

TEST_CASE("Delegate bootstrapping - select multiple spans", "[vectorization-engine]") {
  auto engine = boss::engines::BootstrapEngine();
  REQUIRE(librariesToTest.size() >= 2);
  boss::ExpressionArguments libsArg;
  for(auto it = librariesToTest.begin() + 1; it != librariesToTest.end(); ++it)
    libsArg.emplace_back(*it);
  auto libsExpr = boss::ComplexExpression("List"_, std::move(libsArg));
  auto eval = [&](boss::Expression&& expr) mutable {
    return engine.evaluate(
        "DelegateBootstrapping"_(librariesToTest[0], std::move(libsExpr), std::move(expr)));
  };

  SECTION("Delegate bootstrapping - select multiple spans 1") {
    auto table = "Table"_("key"_(createTwoSpansIntStartingFrom(0)),
                          "payload"_(createTwoSpansIntStartingFrom(4)));
    auto result = eval("Select"_(std::move(table), "Where"_("Greater"_("key"_, 0))));

    CHECK(result == "Table"_("key"_("List"_(1, 2, 3)), "payload"_("List"_(5, 6, 7))));
  }

  SECTION("Delegate bootstrapping - select multiple spans 2") {
    auto table = "Table"_("key"_(createTwoSpansIntStartingFrom(0)),
                          "payload"_(createTwoSpansIntStartingFrom(4)));
    auto result = eval("Select"_(std::move(table),
                                 "Where"_("And"_("Greater"_("key"_, 0), "Greater"_(3, "key"_)))));

    CHECK(result == "Table"_("key"_("List"_(1, 2)), "payload"_("List"_(5, 6))));
  }

  SECTION("Delegate bootstrapping - select multiple spans 3") {
    auto table = "Table"_("key"_(createTwoSpansIntStartingFrom(0)),
                          "payload"_(createTwoSpansIntStartingFrom(4)));
    auto result = eval("Select"_(
        std::move(table), "Where"_("And"_("Greater"_("key"_, 0), "Greater"_(7, "payload"_)))));

    CHECK(result == "Table"_("key"_("List"_(1, 2)), "payload"_("List"_(5, 6))));
  }

  SECTION("Delegate bootstrapping - select four spans") {
    auto table = "Table"_("key"_(createFourSpansIntStartingFrom(0)),
                          "payload"_(createFourSpansIntStartingFrom(8)));
    auto result = eval("Select"_(
        std::move(table), "Where"_("And"_("Greater"_("key"_, 2), "Greater"_(15, "payload"_)))));

    CHECK(result == "Table"_("key"_("List"_(4, 5, 6, 4)), "payload"_("List"_(12, 13, 14, 12))));
  }
}

TEST_CASE("Delegate bootstrapping - group multiple spans", "[vectorization-engine]") {
  auto engine = boss::engines::BootstrapEngine();
  REQUIRE(librariesToTest.size() >= 2);
  boss::ExpressionArguments libsArg;
  for(auto it = librariesToTest.begin() + 1; it != librariesToTest.end(); ++it)
    libsArg.emplace_back(*it);
  auto libsExpr = boss::ComplexExpression("List"_, std::move(libsArg));
  auto eval = [&](boss::Expression&& expr) mutable {
    return engine.evaluate(
        "DelegateBootstrapping"_(librariesToTest[0], std::move(libsExpr), std::move(expr)));
  };

  auto table = "Table"_("key"_(createTwoSpansIntStartingFrom(0)),
                        "payload"_(createTwoSpansIntStartingFrom(4)));

  SECTION("Delegate bootstrapping - group sum multiple spans") {
    auto output = eval("Group"_(table.clone(CloneReason::FOR_TESTING), "Sum"_("key"_)));
    CHECK(output == "Table"_("key"_("List"_(6)))); // NOLINT
  }

  SECTION("Delegate bootstrapping - group count multiple spans") {
    auto output = eval("Group"_(table.clone(CloneReason::FOR_TESTING), "Count"_("key"_)));
    CHECK(output == "Table"_("key"_("List"_(4)))); // NOLINT
  }

  SECTION("Delegate bootstrapping - group count multiple spans with grouping") {
    auto output = eval("Group"_(table.clone(CloneReason::FOR_TESTING), "By"_("key"_),
                                "As"_("countKeys"_, "Count"_("key"_))));
    CHECK(output ==
          "Table"_("key"_("List"_(0, 1, 2, 3)), "countKeys"_("List"_(1, 1, 1, 1)))); // NOLINT
  }

  SECTION("Delegate bootstrapping - group count four spans with grouping") {
    auto tableFourSpans = "Table"_("key"_(createFourSpansIntStartingFrom(0)),
                                   "payload"_(createFourSpansIntStartingFrom(8)));

    auto output = eval(
        "Group"_(std::move(tableFourSpans), "By"_("key"_), "As"_("countKeys"_, "Count"_("key"_))));
    CHECK(output == "Table"_("key"_("List"_(0, 1, 2, 4, 5, 6)),
                             "countKeys"_("List"_(2, 1, 1, 2, 1, 1)))); // NOLINT
  }

  SECTION("Delegate bootstrapping - group sum four spans") {
    auto tableFourSpans = "Table"_("key"_(createFourSpansIntStartingFrom(0)),
                                   "payload"_(createFourSpansIntStartingFrom(8)));

    auto output = eval("Group"_(std::move(tableFourSpans), "Sum"_("key"_)));
    CHECK(output == "Table"_("key"_("List"_(22)))); // NOLINT
  }
}

TEST_CASE("Delegate bootstrapping - TPC-H Q6", "[vectorization-engine]") {
  auto engine = boss::engines::BootstrapEngine();
  REQUIRE(librariesToTest.size() >= 2);
  boss::ExpressionArguments libsArg;
  for(auto it = librariesToTest.begin() + 1; it != librariesToTest.end(); ++it)
    libsArg.emplace_back(*it);
  auto libsExpr = boss::ComplexExpression("List"_, std::move(libsArg));
  auto eval = [&](boss::Expression&& expr) mutable {
    return engine.evaluate(
        "DelegateBootstrapping"_(librariesToTest[0], std::move(libsExpr), std::move(expr)));
  };

  auto lineitem =
      "Table"_("L_ORDERKEY"_(createTwoTwoNumIntSpans(1, 1, 2, 3)),              // NOLINT
               "L_PARTKEY"_(createTwoTwoNumIntSpans(1, 2, 3, 4)),               // NOLINT
               "L_SUPPKEY"_(createTwoTwoNumIntSpans(1, 2, 3, 4)),               // NOLINT
               "L_RETURNFLAG"_(createTwoTwoStrStringSpans("N", "N", "A", "A")), // NOLINT
               "L_LINESTATUS"_(createTwoTwoStrStringSpans("O", "O", "F", "F")), // NOLINT
               "L_QUANTITY"_(createTwoTwoNumIntSpans(17, 21, 8, 5)),            // NOLINT
               "L_EXTENDEDPRICE"_(
                   createTwoTwoNumFloatSpans(17954.55, 34850.16, 7712.48, 25284.00)), // NOLINT
               "L_DISCOUNT"_(createTwoTwoNumFloatSpans(0.10, 0.05, 0.06, 0.06)),      // NOLINT
               "L_TAX"_(createTwoTwoNumFloatSpans(0.02, 0.06, 0.02, 0.06)),           // NOLINT
               "L_SHIPDATE"_(createTwoTwoNumIntSpans(8400, 9130, 9861, 9130)));       // NOLINT

  SECTION("Q6 (No Grouping)") {
    auto output = eval("Project"_(
        "Select"_(
            "Project"_(lineitem.clone(CloneReason::FOR_TESTING),
                       "As"_("L_QUANTITY"_, "L_QUANTITY"_, "L_DISCOUNT"_, "L_DISCOUNT"_,
                             "L_SHIPDATE"_, "L_SHIPDATE"_, "L_EXTENDEDPRICE"_, "L_EXTENDEDPRICE"_)),
            "Where"_("And"_("Greater"_(24, "L_QUANTITY"_),      // NOLINT
                            "Greater"_("L_DISCOUNT"_, 0.0499),  // NOLINT
                            "Greater"_(0.07001, "L_DISCOUNT"_), // NOLINT
                            "Greater"_("DateObject"_("1995-12-31"), "L_SHIPDATE"_),
                            "Greater"_("L_SHIPDATE"_, "DateObject"_("1993-12-31"))))),
        "As"_("revenue"_, "Times"_("L_EXTENDEDPRICE"_, "L_DISCOUNT"_))));

    CHECK(output == "Table"_("revenue"_("List"_(34850.16 * 0.05, 25284.00 * 0.06)))); // NOLINT
  }

  SECTION("Q6") {
    auto output = eval("Group"_(
        "Project"_(
            "Select"_("Project"_(lineitem.clone(CloneReason::FOR_TESTING),
                                 "As"_("L_QUANTITY"_, "L_QUANTITY"_, "L_DISCOUNT"_, "L_DISCOUNT"_,
                                       "L_SHIPDATE"_, "L_SHIPDATE"_, "L_EXTENDEDPRICE"_,
                                       "L_EXTENDEDPRICE"_)),
                      "Where"_("And"_("Greater"_(24, "L_QUANTITY"_),      // NOLINT
                                      "Greater"_("L_DISCOUNT"_, 0.0499),  // NOLINT
                                      "Greater"_(0.07001, "L_DISCOUNT"_), // NOLINT
                                      "Greater"_("DateObject"_("1995-12-31"), "L_SHIPDATE"_),
                                      "Greater"_("L_SHIPDATE"_, "DateObject"_("1993-12-31"))))),
            "As"_("revenue"_, "Times"_("L_EXTENDEDPRICE"_, "L_DISCOUNT"_))),
        "Sum"_("revenue"_)));

    CHECK(output == "Table"_("revenue"_("List"_(34850.16 * 0.05 + 25284.00 * 0.06)))); // NOLINT
  }
}

TEST_CASE("Delegate bootstrapping - more complex queries (without Join)",
          "[vectorization-engine]") {
  auto engine = boss::engines::BootstrapEngine();
  REQUIRE(librariesToTest.size() >= 2);
  boss::ExpressionArguments libsArg;
  for(auto it = librariesToTest.begin() + 1; it != librariesToTest.end(); ++it)
    libsArg.emplace_back(*it);
  auto libsExpr = boss::ComplexExpression("List"_, std::move(libsArg));
  auto eval = [&](boss::Expression&& expr) mutable {
    return engine.evaluate(
        "DelegateBootstrapping"_(librariesToTest[0], std::move(libsExpr), std::move(expr)));
  };

  auto lineitem =
      "Table"_("L_ORDERKEY"_(createTwoTwoNumIntSpans(1, 1, 2, 3)),              // NOLINT
               "L_PARTKEY"_(createTwoTwoNumIntSpans(1, 2, 3, 4)),               // NOLINT
               "L_SUPPKEY"_(createTwoTwoNumIntSpans(1, 2, 3, 4)),               // NOLINT
               "L_RETURNFLAG"_(createTwoTwoStrStringSpans("N", "N", "A", "A")), // NOLINT
               "L_LINESTATUS"_(createTwoTwoStrStringSpans("O", "O", "F", "F")), // NOLINT
               "L_QUANTITY"_(createTwoTwoNumIntSpans(17, 21, 8, 5)),            // NOLINT
               "L_EXTENDEDPRICE"_(
                   createTwoTwoNumFloatSpans(17954.55, 34850.16, 7712.48, 25284.00)), // NOLINT
               "L_DISCOUNT"_(createTwoTwoNumFloatSpans(0.10, 0.05, 0.06, 0.06)),      // NOLINT
               "L_TAX"_(createTwoTwoNumFloatSpans(0.02, 0.06, 0.02, 0.06)),           // NOLINT
               "L_SHIPDATE"_(createTwoTwoNumIntSpans(8400, 9130, 9861, 9130)));       // NOLINT

  SECTION("Multiple selects and groups") {
    auto output = eval("Select"_(
        "Group"_(
            "Select"_(
                "Group"_("Select"_("Project"_(lineitem.clone(CloneReason::FOR_TESTING),
                                              "As"_("L_QUANTITY"_, "L_QUANTITY"_, "L_DISCOUNT"_,
                                                    "L_DISCOUNT"_, "L_SHIPDATE"_, "L_SHIPDATE"_,
                                                    "L_EXTENDEDPRICE"_, "L_EXTENDEDPRICE"_)),
                                   "Where"_("And"_("Greater"_(24, "L_QUANTITY"_), // NOLINT
                                                   "Greater"_("L_DISCOUNT"_, 0.052)))),
                         "By"_("L_QUANTITY"_), "Sum"_("L_EXTENDEDPRICE"_)),
                "Where"_("Greater"_("L_QUANTITY"_, 6))),
            "As"_("count"_, "Count"_("L_QUANTITY"_))),
        "Where"_("Greater"_("count"_, 1))));

    CHECK(output == "Table"_("count"_("List"_(2)))); // NOLINT
  }
}

auto createTwoSpansInt = [](intType n1, intType n2) {
  using SpanArguments = boss::expressions::ExpressionSpanArguments;
  std::vector<intType> v1 = {n1, n1 + 1, n1 + 2};
  std::vector<intType> v2 = {n2, n2 + 1, n2 + 2};
  auto s1 = boss::Span<intType>(std::move(v1));
  auto s2 = boss::Span<intType>(std::move(v2));
  SpanArguments args;
  args.emplace_back(std::move(s1));
  args.emplace_back(std::move(s2));
  return boss::expressions::ComplexExpression("List"_, {}, {}, std::move(args));
};

TEST_CASE("Delegate bootstrapping - join", "[vectorization-engine]") {
  auto engine = boss::engines::BootstrapEngine();
  REQUIRE(librariesToTest.size() >= 2);
  boss::ExpressionArguments libsArg;
  for(auto it = librariesToTest.begin() + 1; it != librariesToTest.end(); ++it)
    libsArg.emplace_back(*it);
  auto libsExpr = boss::ComplexExpression("List"_, std::move(libsArg));
  auto eval = [&](boss::Expression&& expr) mutable {
    return engine.evaluate(
        "DelegateBootstrapping"_(librariesToTest[0], std::move(libsExpr), std::move(expr)));
  };

  SECTION("Simple join 1") {
    auto intTable1 = "Table"_("L_key"_(createTwoSpansInt(1, 100)),
                              "L_value"_(createTwoSpansInt(1, 4))); // NOLINT
    auto intTable2 = "Table"_("O_key"_(createTwoSpansInt(10000, 1)),
                              "O_value"_(createTwoSpansInt(1, 4))); // NOLINT
    auto result = eval("Join"_(std::move(intTable1), std::move(intTable2),
                               "Where"_("Equal"_("L_key"_, "O_key"_))));

    CHECK(result == "Join"_("RadixPartition"_("Table"_("L_value"_("List"_(1, 2, 3, 4, 5, 6))),
                                              "L_key"_("List"_(1, 2, 3)), 0, 1, 2),
                            "RadixPartition"_("Table"_("O_value"_("List"_(1, 2, 3, 4, 5, 6))),
                                              "O_key"_("List"_(1, 2, 3)), 3, 4, 5),
                            "Where"_("Equal"_("L_key"_, "O_key"_))));
  }
}

int main(int argc, char* argv[]) {
  Catch::Session session;
  session.configData().showSuccessfulTests = true;
  session.cli(session.cli() | Catch::clara::Opt(librariesToTest, "library")["--library"]);
  auto const returnCode = session.applyCommandLine(argc, argv);
  if(returnCode != 0) {
    return returnCode;
  }
  return session.run();
}
// NOLINTEND(readability-function-cognitive-complexity)
// NOLINTEND(bugprone-exception-escape)
// NOLINTEND(readability-magic-numbers)