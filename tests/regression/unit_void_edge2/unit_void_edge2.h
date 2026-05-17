#ifndef INCLUDED_UNIT_VOID_EDGE2
#define INCLUDED_UNIT_VOID_EDGE2

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct UnitVoidEdge2 {
  static unsigned int take_unit(std::monostate _x);
  static void opaque_unit(unsigned int _x);
  static unsigned int let_use_as_arg(unsigned int n);
  static void let_return_unit(unsigned int _x0);
  static unsigned int let_match_unit(unsigned int n);
  static unsigned int let_chain_use(unsigned int n);
  static unsigned int let_use_in_if(unsigned int n, bool flag);
  static void mono_bind_return();
  static void mono_bind_rebind();
  static void mono_chain();
  static unsigned int mono_bind_match();
  static unsigned int mono_bind_opaque();
  static void count_down_unit(unsigned int n);
  static inline const unsigned int call_fixpoint = 7u;
  static inline const unsigned int fixpoint_result_used = []() {
    count_down_unit(50u);
    std::monostate x = std::monostate{};
    return take_unit(x);
  }();

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, unsigned int &>
  static unsigned int call_and_discard(F0 &&, unsigned int n) {
    return n;
  }

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, unsigned int &>
  static unsigned int call_and_use(F0 &&f, unsigned int n) {
    f(n);
    std::monostate x = std::monostate{};
    return take_unit(x);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 apply(F0 &&f, T1 _x0) {
    return f(_x0);
  }

  static inline const unsigned int apply_take_unit =
      apply<std::monostate, unsigned int>(take_unit, std::monostate{});
  static std::optional<std::monostate> make_some_unit(bool b);
  static unsigned int use_option_unit(const std::optional<std::monostate> &o);
  static unsigned int compose_option_unit(bool b1, bool b2);

  template <typename A, typename B> struct pair {
    // TYPES
    struct Pair0 {
      A a0;
      B a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    pair() {}

    explicit pair(Pair0 _v) : v_(std::move(_v)) {}

    pair(const pair<A, B> &_other) : v_(std::move(_other.clone().v_)) {}

    pair(pair<A, B> &&_other) : v_(std::move(_other.v_)) {}

    pair<A, B> &operator=(const pair<A, B> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    pair<A, B> &operator=(pair<A, B> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    pair<A, B> clone() const {
      const auto &[a0, a1] = std::get<Pair0>(this->v());
      return pair<A, B>(Pair0{a0, a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit pair(const pair<_U0, _U1> &_other) {
      const auto &[a0, a1] =
          std::get<typename pair<_U0, _U1>::Pair0>(_other.v());
      this->v_ = Pair0{A(a0), B(a1)};
    }

    static pair<A, B> pair0(A a0, B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(a0, a1);
  }

  static pair<unsigned int, std::monostate> make_nat_unit_pair(unsigned int n);

  template <typename T1, typename T2> static T1 get_fst(const pair<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return a0;
  }

  static inline const unsigned int use_pair = []() {
    pair<unsigned int, std::monostate> p = make_nat_unit_pair(7u);
    return get_fst<unsigned int, std::monostate>(std::move(p));
  }();
  static inline const unsigned int test_let_use = let_use_as_arg(5u);
  static inline const unsigned int test_let_match = let_match_unit(3u);
  static inline const unsigned int test_let_chain = let_chain_use(8u);
  static inline const unsigned int test_let_if_t = let_use_in_if(4u, true);
  static inline const unsigned int test_let_if_f = let_use_in_if(4u, false);
  static inline const unsigned int test_call_fix = call_fixpoint;
  static inline const unsigned int test_fix_used = fixpoint_result_used;
  static inline const unsigned int test_call_discard =
      call_and_discard(opaque_unit, 11u);
  static inline const unsigned int test_call_use =
      call_and_use(opaque_unit, 22u);
  static inline const unsigned int test_apply_take = apply_take_unit;
  static inline const unsigned int test_option_use =
      use_option_unit(std::make_optional<std::monostate>(std::monostate{}));
  static inline const unsigned int test_compose =
      compose_option_unit(true, false);
  static inline const unsigned int test_use_pair = use_pair;
};

#endif // INCLUDED_UNIT_VOID_EDGE2
