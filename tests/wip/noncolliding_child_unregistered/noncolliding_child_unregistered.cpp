#include "noncolliding_child_unregistered.h"

bool PeanoNat::leb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return true;
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::leb(*a0, *a00);
    }
  }
}

bool PeanoNat::eq_dec(const Nat &n, const Nat &m) {
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
      bool s = PeanoNat::eq_dec(*a0, *a00);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool AstLib::RawIDOrd::eq_dec(AstLib::RawIDOrd::t x0_,
                              AstLib::RawIDOrd::t x1_) {
  return x0_.raw_id_dec(std::move(x1_));
}

bool AstLib::eq_dec_raw_id(const Raw_id &a, const Raw_id &b) {
  if (RawIDOrd::eq_dec(a, b)) {
    return true;
  } else {
    return false;
  }
}

Nat AstLib::pick(Nat a, Nat b) {
  if (PeanoNat::leb(a, b)) {
    return b;
  } else {
    return a;
  }
}

bool via_non_colliding(const Raw_id &a, const Raw_id &b) {
  if (RawIDOrd::eq_dec(a, b)) {
    return true;
  } else {
    return false;
  }
}

Nat via_colliding(const Nat &x0_, const Nat &x1_) {
  return AstLib::pick(x0_, x1_);
}

bool via_file(const Raw_id &x0_, const Raw_id &x1_) {
  return AstLib::eq_dec_raw_id(x0_, x1_);
}

Nat keep_coll(const Collider &r) {
  if (std::holds_alternative<typename Collider::Tag0>(r.v())) {
    return Nat::o();
  } else {
    const auto &[a0] = std::get<typename Collider::Tag1>(r.v());
    return a0;
  }
}
