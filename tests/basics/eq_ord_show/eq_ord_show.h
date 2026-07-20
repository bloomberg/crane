#ifndef INCLUDED_EQ_ORD_SHOW
#define INCLUDED_EQ_ORD_SHOW

#include <concepts>
#include <string>
#include <utility>

using namespace std::string_literals;

template <typename I, typename A>
concept Eq = requires {
  { I::eqb(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
  {
    I::neqb(std::declval<A>(), std::declval<A>())
  } -> std::convertible_to<bool>;
};
template <typename I, typename A>
concept Ord = requires {
  { I::lt(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
  { I::le(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
  { I::gt(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
  { I::ge(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};
template <typename I, typename A>
concept Show = requires {
  { I::show(std::declval<A>()) } -> std::convertible_to<std::string>;
};

struct NatEq {
  static bool eqb(uint64_t a0, uint64_t a1) { return a0 == a1; }

  static bool neqb(uint64_t x, uint64_t y) { return !(x == y); }
};

static_assert(Eq<NatEq, uint64_t>);

struct NatOrd {
  static bool lt(uint64_t a0, uint64_t a1) { return a0 < a1; }

  static bool le(uint64_t a0, uint64_t a1) { return a0 <= a1; }

  static bool gt(uint64_t x, uint64_t y) { return y < x; }

  static bool ge(uint64_t x, uint64_t y) { return y <= x; }
};

static_assert(Ord<NatOrd, uint64_t>);

struct NatShow {
  static std::string show(uint64_t) { return "<nat>"; }
};

static_assert(Show<NatShow, uint64_t>);

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
bool is_equal(const T1 &x, const T1 &y) {
  return _tcI0::eqb(x, y);
}

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
bool is_different(const T1 &x, const T1 &y) {
  return _tcI0::neqb(x, y);
}

template <typename _tcI0, typename _tcI1, typename T1>
  requires Ord<_tcI0, T1> && Eq<_tcI1, T1>
bool is_less_than(const T1 &x, const T1 &y) {
  return _tcI0::lt(x, y);
}

template <typename _tcI0, typename _tcI1, typename T1>
  requires Ord<_tcI0, T1> && Eq<_tcI1, T1>
bool is_less_or_equal(const T1 &x, const T1 &y) {
  return _tcI0::le(x, y);
}
enum class Ordering { LT, EQ, GT };

template <typename _tcI0, typename _tcI1, typename T1>
  requires Ord<_tcI0, T1> && Eq<_tcI1, T1>
Ordering compare(const T1 &x, const T1 &y) {
  if (_tcI0::lt(x, y)) {
    return Ordering::LT;
  } else {
    if (_tcI1::eqb(x, y)) {
      return Ordering::EQ;
    } else {
      return Ordering::GT;
    }
  }
}

template <typename _tcI0, typename T1>
  requires Show<_tcI0, T1>
std::string to_string(const T1 &x) {
  return _tcI0::show(x);
}

template <typename _tcI0, typename _tcI1, typename T1>
  requires Show<_tcI0, T1> && Eq<_tcI1, T1>
std::string show_if_equal(const T1 &x, const T1 &y) {
  if (_tcI1::eqb(x, y)) {
    return _tcI0::show(x);
  } else {
    return "not equal";
  }
}

template <typename _tcI0, typename _tcI1, typename _tcI2, typename T1>
  requires Show<_tcI0, T1> && Ord<_tcI1, T1> && Eq<_tcI2, T1>
std::string show_comparison(const T1 &x, const T1 &y) {
  if (_tcI1::lt(x, y)) {
    return _tcI0::show(x) + " < "s + _tcI0::show(y);
  } else {
    if (_tcI2::eqb(x, y)) {
      return _tcI0::show(x) + " = "s + _tcI0::show(y);
    } else {
      return _tcI0::show(x) + " > "s + _tcI0::show(y);
    }
  }
}

const bool test_eq_true = is_equal<NatEq, uint64_t>(UINT64_C(42), UINT64_C(42));
const bool test_eq_false =
    is_equal<NatEq, uint64_t>(UINT64_C(42), UINT64_C(43));
const bool test_neq_true =
    is_different<NatEq, uint64_t>(UINT64_C(42), UINT64_C(43));
const bool test_neq_false =
    is_different<NatEq, uint64_t>(UINT64_C(42), UINT64_C(42));
const bool test_lt_true =
    is_less_than<NatOrd, NatEq, uint64_t>(UINT64_C(10), UINT64_C(20));
const bool test_lt_false =
    is_less_than<NatOrd, NatEq, uint64_t>(UINT64_C(20), UINT64_C(10));
const Ordering test_compare_lt =
    compare<NatOrd, NatEq, uint64_t>(UINT64_C(10), UINT64_C(20));
const Ordering test_compare_eq =
    compare<NatOrd, NatEq, uint64_t>(UINT64_C(15), UINT64_C(15));
const Ordering test_compare_gt =
    compare<NatOrd, NatEq, uint64_t>(UINT64_C(20), UINT64_C(10));
const std::string test_show = to_string<NatShow, uint64_t>(UINT64_C(42));

#endif // INCLUDED_EQ_ORD_SHOW
