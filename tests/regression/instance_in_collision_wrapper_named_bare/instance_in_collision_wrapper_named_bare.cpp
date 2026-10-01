#include "instance_in_collision_wrapper_named_bare.h"

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

Nat AstLike::combine(const Nat &x0_, const Nat &x1_) { return x0_.add(x1_); }

bool AstLike::eq(const Nat &x0_, const Nat &x1_) {
  return PeanoNat::eqb(x0_, x1_);
}

Ident to_ident(const AstLike::Raw_id &k) {
  if (std::holds_alternative<typename AstLike::Raw_id::Name>(k.v())) {
    const auto &[n0] = std::get<typename AstLike::Raw_id::Name>(k.v());
    return Ident::global(n0);
  } else {
    const auto &[n0] = std::get<typename AstLike::Raw_id::Anon>(k.v());
    return Ident::local(n0);
  }
}

std::pair<Nat, std::optional<Nat>>
find(const AstLike::Raw_id &k, const List<std::pair<AstLike::Raw_id, Nat>> &l) {
  return std::make_pair(
      k.describe(),
      Lookup::template assoc<AstLike::eq_dec_raw_id, AstLike::Raw_id, Nat>(k,
                                                                           l));
}

std::pair<Ident, std::pair<Nat, std::optional<Nat>>>
both(const AstLike::Raw_id &k, const List<std::pair<AstLike::Raw_id, Nat>> &l) {
  return std::make_pair(to_ident(k), find(k, l));
}

std::pair<Nat, std::optional<Nat>>
both_at_one_site(const AstLike::Raw_id &k,
                 const List<std::pair<AstLike::Raw_id, Nat>> &l) {
  return std::make_pair(
      AstLike::combine(k.describe(), Nat::s(Nat::o())),
      Lookup::template assoc<AstLike::eq_dec_raw_id, AstLike::Raw_id, Nat>(k,
                                                                           l));
}
