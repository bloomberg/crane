#include "file_struct_empty_qualifier.h"

Positive Pos::succ(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xo(succ(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(*a0);
  } else {
    return Positive::xo(Positive::xh());
  }
}

N BinNat::succ(const N &n) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return N::npos(Positive::xh());
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    return N::npos(Pos::succ(a0));
  }
}

N FileStructEmptyQualifier::a(const List<Nat> &x0_) {
  return Helpers::template length<Nat>(x0_);
}

std::optional<List<Nat>> FileStructEmptyQualifier::b(const List<Nat> &l) {
  return Helpers::template map_monad<Monad_option, Nat, Nat>(
      [](Nat x) { return std::make_optional<Nat>(Nat::s(x)); }, l);
}
