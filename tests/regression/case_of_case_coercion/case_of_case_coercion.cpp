#include "case_of_case_coercion.h"

std::string CaseOfCaseCoercion::k1(const List<uint64_t> &l) {
  auto _cs = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      std::optional<std::string> h = std::optional<std::string>();
      return h;
    } else {
      return std::optional<std::string>();
    }
  }();
  if (_cs.has_value()) {
    const std::string &_x = *_cs;
    return "yes";
  } else {
    return "no";
  }
}
