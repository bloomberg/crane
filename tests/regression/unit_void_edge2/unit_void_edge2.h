#ifndef INCLUDED_UNIT_VOID_EDGE2
#define INCLUDED_UNIT_VOID_EDGE2

#include "crane_fn.h"
#include "obj.h"
#include <crane_itree.h>
#include <cstdint>
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

struct UnitVoidEdge2 {
  static uint64_t take_unit(std::monostate _x);
  static void opaque_unit(uint64_t _x);
  static uint64_t let_use_as_arg(uint64_t n);
  static void let_return_unit(uint64_t x0_);
  static uint64_t let_match_unit(uint64_t n);
  static uint64_t let_chain_use(uint64_t n);
  static uint64_t let_use_in_if(uint64_t n, bool flag);
  static void mono_bind_return();
  static void mono_bind_rebind();
  static void mono_chain();
  static uint64_t mono_bind_match();
  static uint64_t mono_bind_opaque();
  static void count_down_unit(uint64_t n);
  static constexpr uint64_t call_fixpoint = UINT64_C(7);
  static constexpr uint64_t fixpoint_result_used = UINT64_C(42);

  template <typename F0> static uint64_t call_and_discard(F0 &&, uint64_t n) {
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
    requires std::is_invocable_r_v<T2, F0 &, T1 &&>
  static T2 apply(F0 &&f, T1 x0_) {
    return f(std::move(x0_));
  }

  static constexpr uint64_t apply_take_unit = UINT64_C(42);
  static std::optional<std::monostate> make_some_unit(bool b);
  static uint64_t use_option_unit(const std::optional<std::monostate> &o);
  static uint64_t compose_option_unit(bool b1, bool b2);

  template <typename A, typename B> struct pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pair<A, B> clone() const { return {a0, a1}; }

    template <typename CraneU0, typename CraneU1>
      requires crane_convertible<CraneU0, const A &> &&
               crane_convertible<CraneU1, const B &>
    operator pair<CraneU0, CraneU1>() const {
      return {crane_convert<CraneU0>(a0), crane_convert<CraneU1>(a1)};
    }

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    return pair_rect<T1, T2, T3>(f, p);
  }

  static pair<uint64_t, std::monostate> make_nat_unit_pair(uint64_t n);

  template <typename T1, typename T2> static T1 get_fst(const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return a0;
  }

  static constexpr uint64_t use_pair = UINT64_C(7);
  static constexpr uint64_t test_let_use = UINT64_C(42);
  static constexpr uint64_t test_let_match = UINT64_C(3);
  static constexpr uint64_t test_let_chain = UINT64_C(42);
  static constexpr uint64_t test_let_if_t = UINT64_C(42);
  static constexpr uint64_t test_let_if_f = UINT64_C(0);
  static constexpr uint64_t test_call_fix = UINT64_C(7);
  static constexpr uint64_t test_fix_used = UINT64_C(42);
  static constexpr uint64_t test_call_discard = UINT64_C(11);
  static constexpr uint64_t test_call_use = UINT64_C(42);
  static constexpr uint64_t test_apply_take = UINT64_C(42);
  static constexpr uint64_t test_option_use = UINT64_C(42);
  static constexpr uint64_t test_compose = UINT64_C(42);
  static constexpr uint64_t test_use_pair = UINT64_C(7);
};

#endif // INCLUDED_UNIT_VOID_EDGE2
