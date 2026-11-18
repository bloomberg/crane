#include "self_comparison_werror.h"

Comparison Coq_Pos::compare_cont(Comparison r, const Positive &x,
                                 const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return compare_cont(r, *a0, *a00);
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return compare_cont(Comparison::GT, *a0, *a00);
    } else {
      return Comparison::GT;
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return compare_cont(Comparison::LT, *a0, *a00);
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return compare_cont(r, *a0, *a00);
    } else {
      return Comparison::GT;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y.v())) {
      return r;
    } else {
      return Comparison::LT;
    }
  }
}

Comparison Coq_Pos::compare(const Positive &x0_, const Positive &x1_) {
  return compare_cont(Comparison::EQ, x0_, x1_);
}

bool Coq_Pos::eqb(const Positive &p, const Positive &q) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return eqb(*a0, *a00);
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return eqb(*a0, *a00);
    } else {
      return false;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(q.v())) {
      return true;
    } else {
      return false;
    }
  }
}

bool Coq_Pos::leb(const Positive &x, const Positive &y) {
  switch (compare(x, y)) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

bool Coq_Pos::ltb(const Positive &x, const Positive &y) {
  switch (compare(x, y)) {
  case Comparison::LT: {
    return true;
  }
  default: {
    return false;
  }
  }
}

Comparison Pos::compare_cont(Comparison r, const Positive &x,
                             const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return compare_cont(r, *a0, *a00);
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return compare_cont(Comparison::GT, *a0, *a00);
    } else {
      return Comparison::GT;
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return compare_cont(Comparison::LT, *a0, *a00);
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return compare_cont(r, *a0, *a00);
    } else {
      return Comparison::GT;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y.v())) {
      return r;
    } else {
      return Comparison::LT;
    }
  }
}

Comparison Pos::compare(const Positive &x0_, const Positive &x1_) {
  return compare_cont(Comparison::EQ, x0_, x1_);
}

bool Pos::eqb(const Positive &p, const Positive &q) {
  if (std::holds_alternative<typename Positive::XI>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(p.v());
    if (std::holds_alternative<typename Positive::XI>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(q.v());
      return eqb(*a0, *a00);
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(p.v());
    if (std::holds_alternative<typename Positive::XO>(q.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(q.v());
      return eqb(*a0, *a00);
    } else {
      return false;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(q.v())) {
      return true;
    } else {
      return false;
    }
  }
}

Comparison BinNat::compare(const N &n, const N &m) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return Comparison::EQ;
    } else {
      return Comparison::LT;
    }
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return Comparison::GT;
    } else {
      const auto &[a00] = std::get<typename N::Npos>(m.v());
      return Pos::compare(a0, a00);
    }
  }
}

bool BinNat::leb(const N &x, const N &y) {
  switch (BinNat::compare(x, y)) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

bool BinNat::eqb(const N &n, const N &m) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename N::Npos>(m.v());
      return Pos::eqb(a0, a00);
    }
  }
}

bool BinNat::ltb(const N &x, const N &y) {
  switch (BinNat::compare(x, y)) {
  case Comparison::LT: {
    return true;
  }
  default: {
    return false;
  }
  }
}

Comparison BinInt::compare(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Comparison::EQ;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      return Comparison::LT;
    } else {
      return Comparison::GT;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Pos::compare(a0, a00);
    } else {
      return Comparison::GT;
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Datatypes::CompOpp(Pos::compare(a0, a00));
    } else {
      return Comparison::LT;
    }
  }
}

bool BinInt::leb(const Z &x, const Z &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

bool BinInt::ltb(const Z &x, const Z &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::LT: {
    return true;
  }
  default: {
    return false;
  }
  }
}

bool BinInt::eqb(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Pos::eqb(a0, a00);
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Pos::eqb(a0, a00);
    } else {
      return false;
    }
  }
}

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Nat.leb n n (and Nat.eqb n n, Nat.ltb n n) prints n <= n; clang's
/// -Wtautological-compare rejects that under the test suite's -Werror.  The
/// value is right; the generated code does not build with Crane's own flags.
///
/// Fixed in Core: simpl folds a pure comparison of one variable with
/// itself to its value (Nat, N, Pos, Z leb/eqb/ltb, Bool.eqb).
/// It missed the argument of a recursive call (rec_arg) and two equal
/// projection chains of one variable (proj_le_self).
bool SelfComparisonWerror::le_self(uint64_t) { return true; }

bool SelfComparisonWerror::eq_self(uint64_t _x) { return le_self(_x); }

bool SelfComparisonWerror::lt_self(uint64_t) { return false; }

bool SelfComparisonWerror::bool_eq_self(bool) { return true; }

bool SelfComparisonWerror::z_le_self(const Z &) { return true; }

bool SelfComparisonWerror::z_eq_self(const Z &_x) { return z_le_self(_x); }

bool SelfComparisonWerror::z_lt_self(const Z &) { return false; }

bool SelfComparisonWerror::n_le_self(const N &) { return true; }

bool SelfComparisonWerror::n_eq_self(const N &_x) { return n_le_self(_x); }

bool SelfComparisonWerror::n_lt_self(const N &) { return false; }

bool SelfComparisonWerror::pos_le_self(const Positive &) { return true; }

bool SelfComparisonWerror::pos_eq_self(const Positive &_x) {
  return pos_le_self(_x);
}

bool SelfComparisonWerror::pos_lt_self(const Positive &) { return false; }

/// The comparison as the argument of a recursive call.
bool SelfComparisonWerror::rec_arg(const List<uint64_t> &l, uint64_t, bool b) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return b;
  } else {
    const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return rec_arg(*a1, UINT64_C(0), true);
  }
}

/// The same pure projection of one variable on both sides.
bool SelfComparisonWerror::proj_le_self(const SelfComparisonWerror::pt &) {
  return true;
}

Comparison Datatypes::CompOpp(Comparison r) {
  switch (r) {
  case Comparison::EQ: {
    return Comparison::EQ;
  }
  case Comparison::LT: {
    return Comparison::GT;
  }
  case Comparison::GT: {
    return Comparison::LT;
  }
  default:
    std::unreachable();
  }
}
