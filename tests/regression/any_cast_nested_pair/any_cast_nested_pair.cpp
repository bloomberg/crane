#include "any_cast_nested_pair.h"

AnyCastNestedPair::SemVal AnyCastNestedPair::mkSemVal(uint64_t) {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsRegression.any_cast_nested_pair."
                         "AnyCastNestedPair.AnyCastNestedPair.mkSemVal");
}

uint64_t AnyCastNestedPair::getSemVal(AnyCastNestedPair::SemVal) {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsRegression.any_cast_nested_pair."
                         "AnyCastNestedPair.AnyCastNestedPair.getSemVal");
}

uint64_t AnyCastNestedPair::apply_pred(AnyCastNestedPair::symbols_semty input) {
  auto _cs = std::any_cast<std::pair<std::any, std::any>>(input);
  const auto &v1 = _cs.first;
  const auto &rest = _cs.second;
  const std::any &v2 = std::any_cast<std::pair<std::any, std::any>>(rest).first;
  const std::any &_x =
      std::any_cast<std::pair<std::any, std::any>>(rest).second;
  return (getSemVal(v1) +
          getSemVal(std::any_cast<AnyCastNestedPair::SemVal>(v2)));
}

uint64_t AnyCastNestedPair::test_pred(uint64_t a, uint64_t b) {
  return apply_pred(std::make_pair(
      mkSemVal(a), std::make_pair(mkSemVal(b), std::monostate{})));
}
