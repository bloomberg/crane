#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <cmath>
#include <crane_int63.h>
#include <cstdint>
#include <limits>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
enum class Comparison;
template <typename A> struct Carry;
enum class Float_comparison;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

enum class Comparison { EQ, LT, GT };

template <typename A> struct Carry {
  // TYPES
  struct C0 {
    A a0;
  };

  struct C1 {
    A a0;
  };

  using variant_t = std::variant<C0, C1>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Carry() {}

  explicit Carry(C0 _v) : v_(std::move(_v)) {}

  explicit Carry(C1 _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  Carry(const Carry<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Carry<CraneU>::C0>(_other.v())) {
            const auto &[a0] = std::get<typename Carry<CraneU>::C0>(_other.v());
            return C0{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] = std::get<typename Carry<CraneU>::C1>(_other.v());
            return C1{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Carry<A> c0(A a0) { return Carry<A>(C0{std::move(a0)}); }

  static Carry<A> c1(A a0) { return Carry<A>(C1{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

enum class Float_comparison { FEQ, FLT, FGT, FNOTCOMPARABLE };

struct PrimInt63FloatOps {
  static constexpr int64_t max = INT64_C(9223372036854775807);
  static constexpr int64_t min_s = INT64_C(4611686018427387904);
  static int64_t minus(int64_t x);
  static bool pair_is(std::pair<int64_t, int64_t> p, int64_t a, int64_t b);
  static bool carry_is(const Carry<int64_t> &c, bool high, int64_t v);
  static bool cmp_is(Comparison c, Comparison d);
  static inline const List<bool> int_checks = List<bool>::cons(
      crane::int63_asr(min_s, INT64_C(1)) == INT64_C(6917529027641081856),
      List<bool>::cons(crane::int63_asr(max, INT64_C(70)) == INT64_C(0), List<bool>::cons(crane::int63_asr(INT64_C(40), INT64_C(3)) == INT64_C(5), List<bool>::cons(crane::int63_divs(min_s, max) == min_s, List<bool>::cons(crane::int63_divs(minus(INT64_C(7)), INT64_C(2)) == minus(INT64_C(3)), List<bool>::cons(crane::int63_mods(minus(INT64_C(7)), INT64_C(2)) == minus(INT64_C(1)), List<bool>::cons(crane::int63_divs(INT64_C(5), INT64_C(0)) == INT64_C(0), List<bool>::cons(crane::int63_mods(INT64_C(5), INT64_C(0)) == INT64_C(5), List<bool>::cons(crane::int63_ltsb(minus(INT64_C(1)), INT64_C(0)), List<bool>::cons(!(crane::int63_ltsb(INT64_C(0), minus(INT64_C(1)))), List<bool>::cons(crane::int63_lesb(min_s, minus(INT64_C(1))), List<bool>::cons(cmp_is(crane::int63_compare<Comparison>(max, INT64_C(1)), Comparison::GT), List<bool>::cons(cmp_is(crane::int63_compares<Comparison>(max, INT64_C(1)), Comparison::LT), List<bool>::cons(cmp_is(crane::int63_compares<Comparison>(INT64_C(3), INT64_C(3)), Comparison::EQ), List<bool>::cons(crane::int63_head0(INT64_C(0)) == INT64_C(63), List<bool>::cons(crane::int63_head0(INT64_C(1)) == INT64_C(62), List<bool>::cons(crane::int63_head0(max) == INT64_C(0), List<bool>::cons(crane::int63_tail0(INT64_C(0)) == INT64_C(63), List<bool>::cons(crane::int63_tail0(INT64_C(8)) == INT64_C(3), List<bool>::cons(crane::int63_addmuldiv(INT64_C(0), INT64_C(12), max) == INT64_C(12), List<bool>::cons(crane::int63_addmuldiv(INT64_C(63), INT64_C(12), max) == max, List<bool>::cons(crane::int63_addmuldiv(INT64_C(4), INT64_C(3), max) == INT64_C(63), List<bool>::cons(crane::int63_addmuldiv(INT64_C(70), INT64_C(3), max) == INT64_C(0), List<bool>::cons(pair_is(crane::int63_mulc<std::pair<int64_t, int64_t>>(max, max), INT64_C(9223372036854775806), INT64_C(1)), List<bool>::cons(pair_is(crane::int63_mulc<std::pair<int64_t, int64_t>>(INT64_C(6), INT64_C(7)), INT64_C(0), INT64_C(42)), List<bool>::cons(pair_is(crane::int63_mulc<std::pair<int64_t, int64_t>>(min_s, INT64_C(4)), INT64_C(2), INT64_C(0)), List<bool>::cons(pair_is(crane::int63_diveucl<std::pair<int64_t, int64_t>>(INT64_C(17), INT64_C(5)), INT64_C(3), INT64_C(2)), List<bool>::cons(pair_is(crane::int63_diveucl<std::pair<int64_t, int64_t>>(INT64_C(17), INT64_C(0)), INT64_C(0), INT64_C(17)), List<bool>::cons(pair_is(crane::int63_diveucl_21<std::pair<int64_t, int64_t>>(INT64_C(3), INT64_C(7), INT64_C(10)), INT64_C(2767011611056432743), INT64_C(1)), List<bool>::cons(pair_is(crane::int63_diveucl_21<std::pair<int64_t, int64_t>>(INT64_C(10), INT64_C(0), INT64_C(3)), INT64_C(0), INT64_C(0)), List<bool>::cons(carry_is(crane::int63_addc<Carry<int64_t>>(max, INT64_C(1)), true, INT64_C(0)), List<bool>::cons(carry_is(crane::int63_addc<Carry<int64_t>>(INT64_C(1), INT64_C(2)), false, INT64_C(3)), List<bool>::cons(carry_is(crane::int63_addcarryc<Carry<int64_t>>(max, INT64_C(0)), true, INT64_C(0)), List<bool>::cons(carry_is(crane::int63_addcarryc<Carry<int64_t>>(INT64_C(1), INT64_C(2)), false, INT64_C(4)), List<bool>::cons(carry_is(crane::int63_subc<Carry<int64_t>>(INT64_C(0), INT64_C(1)), true, max), List<bool>::cons(carry_is(crane::int63_subc<Carry<int64_t>>(INT64_C(5), INT64_C(5)), false, INT64_C(0)), List<bool>::cons(carry_is(crane::int63_subcarryc<Carry<int64_t>>(INT64_C(5), INT64_C(4)), false, INT64_C(0)), List<bool>::cons(carry_is(crane::int63_subcarryc<Carry<int64_t>>(INT64_C(4), INT64_C(4)), true, max), List<bool>::nil()))))))))))))))))))))))))))))))))))))));
  static bool fcmp_is(Float_comparison c, Float_comparison d);
  static inline const double nan = 0x0p+0 / 0x0p+0;
  static inline const List<bool> float_checks = List<bool>::cons(
      fcmp_is(static_cast<Float_comparison>(
          0x1p+0 < 0x1p+1 ? 1
                          : (0x1p+0 > 0x1p+1 ? 2 : (0x1p+0 == 0x1p+1 ? 0 : 3))),
              Float_comparison::FLT),
      List<bool>::cons(
          fcmp_is(static_cast<Float_comparison>(
              0x1p+1 < 0x1p+0
                  ? 1
                  : (0x1p+1 > 0x1p+0 ? 2 : (0x1p+1 == 0x1p+0 ? 0 : 3))),
                  Float_comparison::FGT),
          List<bool>::cons(
              fcmp_is(static_cast<Float_comparison>(
                  0x0p+0 < -0x0p+0
                      ? 1
                      : (0x0p+0 > -0x0p+0 ? 2 : (0x0p+0 == -0x0p+0 ? 0 : 3))),
                      Float_comparison::FEQ),
              List<bool>::cons(
                  fcmp_is(static_cast<Float_comparison>(
                      nan < 0x1p+0
                          ? 1
                          : (nan > 0x1p+0 ? 2 : (nan == 0x1p+0 ? 0 : 3))),
                          Float_comparison::FNOTCOMPARABLE),
                  List<bool>::cons(
                      (std::fabs(0x1.8p-1) >= (0.5) &&
                       std::fabs(0x1.8p-1) < (1.0) ? static_cast<int64_t>(
                                                         std::ldexp(std::fabs(
                                                             0x1.8p-1),
                                                                    53))
                                                   : 0) ==
                      INT64_C(6755399441055744),
                      List<bool>::cons(
                          (std::fabs(-0x1p-1) >= (0.5) &&
                           std::fabs(-0x1p-1) < (1.0) ? static_cast<int64_t>(
                                                            std::ldexp(
                                                                std::fabs(
                                                                    -0x1p-1),
                                                                53))
                                                      : 0) ==
                          INT64_C(4503599627370496),
                          List<bool>::cons(
                              (std::fabs(0x1p+1) >= (0.5) &&
                               std::fabs(0x1p+1) < (1.0) ? static_cast<int64_t>(
                                                               std::ldexp(
                                                                   std::fabs(
                                                                       0x1p+1),
                                                                   53))
                                                         : 0) ==
                              INT64_C(0),
                              List<bool>::cons(
                                  (std::isfinite(0x1.8p+1) &&
                                   0x1.8p+1 != 0.0
                                       ? std::pair<double, int64_t>(
                                             std::scalbn(
                                                 0x1.8p+1,
                                                 -(std::ilogb(0x1.8p+1) + 1)),
                                             static_cast<int64_t>(
                                                 std::ilogb(0x1.8p+1)) +
                                             2102)
                                       : std::pair<double, int64_t>(0x1.8p+1,
                                                                    0))
                                      .first ==
                                  0x1.8p-1,
                                  List<bool>::cons(
                                      (std::isfinite(0x1.8p+1) &&
                                       0x1.8p+1 != 0.0
                                           ? std::pair<double, int64_t>(
                                                 std::scalbn(
                                                     0x1.8p+1,
                                                     -(std::ilogb(0x1.8p+1) +
                                                       1)),
                                                 static_cast<int64_t>(
                                                     std::ilogb(0x1.8p+1)) +
                                                 2102)
                                           : std::pair<double, int64_t>(
                                                 0x1.8p+1, 0))
                                          .second ==
                                      INT64_C(2103),
                                      List<bool>::cons(
                                          (std::isfinite(0x0p+0) &&
                                           0x0p+0 != 0.0
                                               ? std::pair<double, int64_t>(
                                                     std::scalbn(
                                                         0x0p+0,
                                                         -(std::ilogb(0x0p+0) +
                                                           1)),
                                                     static_cast<int64_t>(
                                                         std::ilogb(0x0p+0)) +
                                                     2102)
                                               : std::pair<double, int64_t>(
                                                     0x0p+0, 0))
                                              .second ==
                                          INT64_C(0),
                                          List<bool>::cons(
                                              std::ldexp(
                                                  0x1.8p-1,
                                                  static_cast<int32_t>(
                                                      std::min<int64_t>(
                                                          INT64_C(2103), 4202) -
                                                      2101)) ==
                                              0x1.8p+1,
                                              List<bool>::cons(
                                                  std::ldexp(
                                                      0x1p+0,
                                                      static_cast<int32_t>(
                                                          std::min<int64_t>(
                                                              max, 4202) -
                                                          2101)) ==
                                                  std::ldexp(
                                                      0x1p+0,
                                                      static_cast<int32_t>(
                                                          std::min<int64_t>(
                                                              INT64_C(4202),
                                                              4202) -
                                                          2101)),
                                                  List<bool>::cons(
                                                      std::nextafter(
                                                          0x1p+0,
                                                          std::numeric_limits<
                                                              double>::infinity()) ==
                                                      0x1.0000000000001p+0,
                                                      List<bool>::cons(
                                                          std::nextafter(
                                                              0x1p+0,
                                                              -std::numeric_limits<
                                                                  double>::infinity()) ==
                                                          0x1.fffffffffffffp-1,
                                                          List<bool>::cons(
                                                              std::nextafter(
                                                                  0x0p+0,
                                                                  -std::numeric_limits<
                                                                      double>::infinity()) <
                                                              0x0p+0,
                                                              List<bool>::cons(
                                                                  std::nextafter(
                                                                      -0x1.fffffffffffffp+1023,
                                                                      std::numeric_limits<
                                                                          double>::infinity()) ==
                                                                  -0x1.ffffffffffffep+1023,
                                                                  List<bool>::nil()))))))))))))))));
  static uint64_t count_true(const List<bool> &l);
  static inline const uint64_t int_passed = count_true(int_checks);
  static inline const uint64_t int_total = int_checks.length();
  static inline const uint64_t float_passed = count_true(float_checks);
  static inline const uint64_t float_total = float_checks.length();
};
