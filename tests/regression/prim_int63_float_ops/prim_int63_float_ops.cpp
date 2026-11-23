#include "prim_int63_float_ops.h"

int64_t PrimInt63FloatOps::minus(int64_t x) {
  return static_cast<int64_t>(
      (static_cast<uint64_t>(INT64_C(0)) - static_cast<uint64_t>(x)) &
      0x7FFFFFFFFFFFFFFFULL);
}

bool PrimInt63FloatOps::pair_is(std::pair<int64_t, int64_t> p, int64_t a,
                                int64_t b) {
  return (p.first == a && p.second == b);
}

bool PrimInt63FloatOps::carry_is(const Carry<int64_t> &c, bool high,
                                 int64_t v) {
  if (std::holds_alternative<typename Carry<int64_t>::C0>(c.v())) {
    const auto &[a0] = std::get<typename Carry<int64_t>::C0>(c.v());
    return (!(high) && a0 == v);
  } else {
    const auto &[a0] = std::get<typename Carry<int64_t>::C1>(c.v());
    return (high && a0 == v);
  }
}

bool PrimInt63FloatOps::cmp_is(Comparison c, Comparison d) {
  switch (c) {
  case Comparison::EQ: {
    switch (d) {
    case Comparison::EQ: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Comparison::LT: {
    switch (d) {
    case Comparison::LT: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Comparison::GT: {
    switch (d) {
    case Comparison::GT: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  default:
    std::unreachable();
  }
}

bool PrimInt63FloatOps::fcmp_is(Float_comparison c, Float_comparison d) {
  switch (c) {
  case Float_comparison::FEQ: {
    switch (d) {
    case Float_comparison::FEQ: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Float_comparison::FLT: {
    switch (d) {
    case Float_comparison::FLT: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Float_comparison::FGT: {
    switch (d) {
    case Float_comparison::FGT: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Float_comparison::FNOTCOMPARABLE: {
    switch (d) {
    case Float_comparison::FNOTCOMPARABLE: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  default:
    std::unreachable();
  }
}

uint64_t PrimInt63FloatOps::count_true(const List<bool> &l) {
  if (std::holds_alternative<typename List<bool>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<bool>::Cons>(l.v());
    return ((a0 ? UINT64_C(1) : UINT64_C(0)) + count_true(*a1));
  }
}
