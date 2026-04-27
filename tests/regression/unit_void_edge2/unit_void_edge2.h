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
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct UnitVoidEdge2 {
  __attribute__((pure)) static unsigned int take_unit(const std::monostate &_x);
  static void opaque_unit(const unsigned int &_x);
  __attribute__((pure)) static unsigned int
  let_use_as_arg(const unsigned int &n);
  static void let_return_unit(const unsigned int &_x0);
  __attribute__((pure)) static unsigned int let_match_unit(unsigned int n);
  __attribute__((pure)) static unsigned int
  let_chain_use(const unsigned int &n);
  __attribute__((pure)) static unsigned int let_use_in_if(const unsigned int &n,
                                                          const bool &flag);
  static void mono_bind_return();
  static void mono_bind_rebind();
  static void mono_chain();
  static unsigned int mono_bind_match();
  static unsigned int mono_bind_opaque();
  static void count_down_unit(const unsigned int &n);
  static inline const unsigned int call_fixpoint = 7u;
  static inline const unsigned int fixpoint_result_used = []() {
    count_down_unit(50u);
    std::monostate x = std::monostate{};
    return take_unit(x);
  }();

  template <MapsTo<void, unsigned int> F0>
  __attribute__((pure)) static unsigned int call_and_discard(F0 &&,
                                                             unsigned int n) {
    return n;
  }

  template <MapsTo<void, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  call_and_use(F0 &&f, const unsigned int &n) {
    f(n);
    std::monostate x = std::monostate{};
    return take_unit(x);
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 apply(F0 &&f, const T1 _x0) {
    return f(_x0);
  }

  static inline const unsigned int apply_take_unit =
      apply<std::monostate, unsigned int>(take_unit, std::monostate{});
  __attribute__((pure)) static std::optional<std::monostate>
  make_some_unit(const bool &b);
  __attribute__((pure)) static unsigned int
  use_option_unit(const std::optional<std::monostate> &o);
  __attribute__((pure)) static unsigned int compose_option_unit(const bool &b1,
                                                                const bool &b2);

  template <typename t_A, typename t_B> struct pair {
    // TYPES
    struct Pair0 {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    pair() {}

    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

    pair(const pair<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pair(pair<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    pair<t_A, t_B> &operator=(const pair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    pair<t_A, t_B> &operator=(pair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pair<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Pair0>(_sv.v());
      return pair<t_A, t_B>(Pair0{d_a0, d_a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit pair(const pair<_U0, _U1> &_other) {
      const auto &[d_a0, d_a1] =
          std::get<typename pair<_U0, _U1>::Pair0>(_other.v());
      d_v_ = Pair0{t_A(d_a0), t_B(d_a1)};
    }

    __attribute__((pure)) static pair<t_A, t_B> pair0(t_A a0, t_B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) pair<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const pair<t_A, t_B> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = pair<t_A, t_B>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(d_a0, d_a1);
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(d_a0, d_a1);
  }

  __attribute__((pure)) static pair<unsigned int, std::monostate>
  make_nat_unit_pair(unsigned int n);

  template <typename T1, typename T2> static T1 get_fst(const pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return d_a0;
  }

  static inline const unsigned int use_pair = []() {
    pair<unsigned int, std::monostate> p = make_nat_unit_pair(7u);
    return get_fst<unsigned int, std::monostate>(p);
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
