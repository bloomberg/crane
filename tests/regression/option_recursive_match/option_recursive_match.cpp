#include "option_recursive_match.h"

Nat OptionRecursiveMatch::len(const OptionRecursiveMatch::chain &c) {
  const auto &[a0, a1] =
      std::get<typename OptionRecursiveMatch::chain::C>(c.v());
  auto &&_sv0 = *a1;
  if (std::holds_alternative<
          typename Option<OptionRecursiveMatch::chain>::Some>(_sv0.v())) {
    const auto &[a00] =
        std::get<typename Option<OptionRecursiveMatch::chain>::Some>(_sv0.v());
    return Nat::s(len(a00));
  } else {
    return Nat::s(Nat::o());
  }
}
