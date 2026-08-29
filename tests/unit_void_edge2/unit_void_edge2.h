#ifndef INCLUDED_UNIT_VOID_EDGE2
#define INCLUDED_UNIT_VOID_EDGE2

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct UnitVoidEdge2 {
  static uint64_t take_unit(std::monostate _x);
  static void opaque_unit(uint64_t _x);
  static uint64_t let_use_as_arg(uint64_t n);
  static void let_return_unit(uint64_t _x0);
  static uint64_t let_match_unit(uint64_t n);
  static uint64_t let_chain_use(uint64_t n);
  static uint64_t let_use_in_if(uint64_t n, bool flag);
  static void mono_bind_return();
  static void mono_bind_rebind();
  static void mono_chain();
  static uint64_t mono_bind_match();
  static uint64_t mono_bind_opaque();
  static void count_down_unit(uint64_t n);
  static inline const uint64_t call_fixpoint = UINT64_C(7);
  static inline const uint64_t fixpoint_result_used = []() {
    count_down_unit(UINT64_C(50));
    std::monostate x = std::monostate{};
    return take_unit(x);
  }();

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static uint64_t call_and_discard(F0 &&, uint64_t n) {
    return n;
  }

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static uint64_t call_and_use(F0 &&f, uint64_t n) {
    f(n);
    std::monostate x = std::monostate{};
    return take_unit(x);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 apply(F0 &&f, T1 _x0) {
    return f(_x0);
  }

  static inline const uint64_t apply_take_unit =
      apply<std::monostate, uint64_t>(take_unit, std::monostate{});
  static std::optional<std::monostate> make_some_unit(bool b);
  static uint64_t use_option_unit(const std::optional<std::monostate> &o);
  static uint64_t compose_option_unit(bool b1, bool b2);

  template <typename A, typename B> struct pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pair<A, B> clone() const { return {a0, a1}; }

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  static pair<uint64_t, std::monostate> make_nat_unit_pair(uint64_t n);

  template <typename T1, typename T2> static T1 get_fst(const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return a0;
  }

  static inline const uint64_t use_pair = []() {
    pair<uint64_t, std::monostate> p = make_nat_unit_pair(UINT64_C(7));
    return get_fst<uint64_t, std::monostate>(std::move(p));
  }();
  static inline const uint64_t test_let_use = let_use_as_arg(UINT64_C(5));
  static inline const uint64_t test_let_match = let_match_unit(UINT64_C(3));
  static inline const uint64_t test_let_chain = let_chain_use(UINT64_C(8));
  static inline const uint64_t test_let_if_t = let_use_in_if(UINT64_C(4), true);
  static inline const uint64_t test_let_if_f =
      let_use_in_if(UINT64_C(4), false);
  static inline const uint64_t test_call_fix = call_fixpoint;
  static inline const uint64_t test_fix_used = fixpoint_result_used;
  static inline const uint64_t test_call_discard =
      call_and_discard(opaque_unit, UINT64_C(11));
  static inline const uint64_t test_call_use =
      call_and_use(opaque_unit, UINT64_C(22));
  static inline const uint64_t test_apply_take = apply_take_unit;
  static inline const uint64_t test_option_use =
      use_option_unit(std::make_optional<std::monostate>(std::monostate{}));
  static inline const uint64_t test_compose = compose_option_unit(true, false);
  static inline const uint64_t test_use_pair = use_pair;
};

#endif // INCLUDED_UNIT_VOID_EDGE2
