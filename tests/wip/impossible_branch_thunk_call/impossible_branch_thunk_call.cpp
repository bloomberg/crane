#include "impossible_branch_thunk_call.h"

uint64_t
ImpossibleBranchThunkCall::val(const ImpossibleBranchThunkCall::tagged &t) {
  if (std::holds_alternative<typename ImpossibleBranchThunkCall::tagged::TN>(
          t.v())) {
    const auto &[a0] =
        std::get<typename ImpossibleBranchThunkCall::tagged::TN>(t.v());
    return a0;
  } else {
    const auto &[a0] =
        std::get<typename ImpossibleBranchThunkCall::tagged::TL>(t.v());
    return ([]() -> std::any {
      throw std::logic_error("unreachable");
      return std::any{};
    })()(a0);
  }
}

uint64_t
ImpossibleBranchThunkCall::len(const ImpossibleBranchThunkCall::tagged &t) {
  if (std::holds_alternative<typename ImpossibleBranchThunkCall::tagged::TN>(
          t.v())) {
    const auto &[a0] =
        std::get<typename ImpossibleBranchThunkCall::tagged::TN>(t.v());
    return ([]() -> std::any {
      throw std::logic_error("unreachable");
      return std::any{};
    })()(a0);
  } else {
    const auto &[a0] =
        std::get<typename ImpossibleBranchThunkCall::tagged::TL>(t.v());
    return a0.length();
  }
}

uint64_t ImpossibleBranchThunkCall::run(uint64_t k) {
  return (val(tagged::tn((k + UINT64_C(3)))) +
          len(tagged::tl(List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())))));
}
