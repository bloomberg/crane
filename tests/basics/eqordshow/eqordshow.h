#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename I, typename A>
concept Eq = requires(A a0, A a1) {
  { I::eqb(a1, a0) } -> std::convertible_to<bool>;
  { I::neqb(a1, a0) } -> std::convertible_to<bool>;
};

template <typename I, typename A>
concept Ord = requires(A a0, A a1) {
  { I::lt(a1, a0) } -> std::convertible_to<bool>;
  { I::le(a1, a0) } -> std::convertible_to<bool>;
  { I::gt(a1, a0) } -> std::convertible_to<bool>;
  { I::ge(a1, a0) } -> std::convertible_to<bool>;
};

template <typename I, typename A>
concept Show = requires(A a0) {
  { I::show(a0) } -> std::convertible_to<std::string>;
};

struct NatEq {
  static bool eqb(unsigned int a0, unsigned int a1) { return (a0 == a1); }
  static bool neqb(unsigned int x, unsigned int y) { return !((x == y)); }
};
static_assert(Eq<NatEq, unsigned int>);

struct NatOrd {
  static bool lt(unsigned int a0, unsigned int a1) { return (a0 < a1); }
  static bool le(unsigned int a0, unsigned int a1) { return (a0 <= a1); }
  static bool gt(unsigned int x, unsigned int y) { return (y < x); }
  static bool ge(unsigned int x, unsigned int y) { return (y <= x); }
};
static_assert(Ord<NatOrd, unsigned int>);

struct NatShow {
  static std::string show(unsigned int _x) { return "<nat>"; }
};
static_assert(Show<NatShow, unsigned int>);

template <typename _tcI0, typename T1> bool is_equal(const T1 x, const T1 y) {
  return _tcI0::eqb(x, y);
}

template <typename _tcI0, typename T1>
bool is_different(const T1 x, const T1 y) {
  return _tcI0::neqb(x, y);
}

template <typename _tcI0, typename _tcI1, typename T1>
bool is_less_than(const T1 x, const T1 y) {
  return _tcI0::lt(x, y);
}

template <typename _tcI0, typename _tcI1, typename T1>
bool is_less_or_equal(const T1 x, const T1 y) {
  return _tcI0::le(x, y);
}

enum class Ordering { LT, EQ, GT };

template <typename _tcI0, typename _tcI1, typename T1>
Ordering compare(const T1 x, const T1 y) {
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

template <typename _tcI0, typename T1> std::string to_string(const T1 x) {
  return _tcI0::show(x);
}

template <typename _tcI0, typename _tcI1, typename T1>
std::string show_if_equal(const T1 x, const T1 y) {
  if (_tcI1::eqb(x, y)) {
    return _tcI0::show(x);
  } else {
    return "not equal";
  }
}

template <typename _tcI0, typename _tcI1, typename _tcI2, typename T1>
std::string show_comparison(const T1 x, const T1 y) {
  if (_tcI1::lt(x, y)) {
    return _tcI0::show(x) + " < " + _tcI0::show(y);
  } else {
    if (_tcI2::eqb(x, y)) {
      return _tcI0::show(x) + " = " + _tcI0::show(y);
    } else {
      return _tcI0::show(x) + " > " + _tcI0::show(y);
    }
  }
}

const bool test_eq_true = is_equal<NatEq, unsigned int>(42u, 42u);

const bool test_eq_false = is_equal<NatEq, unsigned int>(42u, 43u);

const bool test_neq_true = is_different<NatEq, unsigned int>(42u, 43u);

const bool test_neq_false = is_different<NatEq, unsigned int>(42u, 42u);

const bool test_lt_true = is_less_than<NatOrd, NatEq, unsigned int>(10u, 20u);

const bool test_lt_false = is_less_than<NatOrd, NatEq, unsigned int>(20u, 10u);

const Ordering test_compare_lt = compare<NatOrd, NatEq, unsigned int>(10u, 20u);

const Ordering test_compare_eq = compare<NatOrd, NatEq, unsigned int>(15u, 15u);

const Ordering test_compare_gt = compare<NatOrd, NatEq, unsigned int>(20u, 10u);

const std::string test_show = to_string<NatShow, unsigned int>(42u);
