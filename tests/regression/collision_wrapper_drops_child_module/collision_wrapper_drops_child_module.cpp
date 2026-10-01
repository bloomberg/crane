#include "collision_wrapper_drops_child_module.h"

bool PeanoNat::eqb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::eqb(*a0, *a00);
    }
  }
}

bool AstLike::IdentDec::eq_dec(const Nat &x0_, const Nat &x1_) {
  return PeanoNat::eqb(x0_, x1_);
}

bool AstLike::RawIDOrdDec::eq_dec(const Nat &x0_, const Nat &x1_) {
  return PeanoNat::eqb(x0_, x1_);
}

bool AstLike::Ord::cmp(const AstLike::Raw_id &x, const AstLike::Raw_id &y) {
  return PeanoNat::eqb(x.tag(), y.tag());
}

bool AstLike::Ord::compare(const AstLike::Raw_id &x, const AstLike::Raw_id &y) {
  return !(AstLike::Ord::cmp(x, y));
}

::Ident to_ident(const AstLike::Raw_id &k) {
  if (std::holds_alternative<typename AstLike::Raw_id::Name>(k.v())) {
    const auto &[n0] = std::get<typename AstLike::Raw_id::Name>(k.v());
    return ::Ident::global(n0);
  } else {
    const auto &[n0] = std::get<typename AstLike::Raw_id::Anon>(k.v());
    return ::Ident::local(n0);
  }
}

std::pair<::Ident, std::pair<std::pair<bool, bool>, bool>>
both(const AstLike::Raw_id &k) {
  return std::make_pair(
      to_ident(k),
      std::make_pair(
          std::make_pair(AstLike::Ident::eq_dec(k.tag(), Nat::s(Nat::o())),
                         AstLike::RawIDOrd::eq_dec(k.tag(), Nat::s(Nat::o()))),
          AstLike::Ord::compare(k, k)));
}
