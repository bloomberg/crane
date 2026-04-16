#ifndef INCLUDED_TUPLE
#define INCLUDED_TUPLE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_B> struct Prod {
  // TYPES
  struct Pair {
    t_A d_a0;
    t_B d_a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Prod<t_A, t_B>> pair(t_A a0, t_B a1) {
    return std::make_shared<Prod<t_A, t_B>>(Pair{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Tuple {
  template <typename a, typename b> using pair = std::shared_ptr<Prod<a, b>>;

  template <typename T1, typename T2>
  static std::shared_ptr<Prod<T1, T2>> make_pair(const T1 a, const T2 b) {
    return Prod<T1, T2>::pair(a, b);
  }

  template <typename T1, typename T2>
  static T1 fst(const std::shared_ptr<Prod<T1, T2>> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Prod<T1, T2>::Pair>(p->v());
    return d_a0;
  }

  template <typename T1, typename T2>
  static T2 snd(const std::shared_ptr<Prod<T1, T2>> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Prod<T1, T2>::Pair>(p->v());
    return d_a1;
  }

  template <typename T1, typename T2>
  static std::shared_ptr<Prod<T2, T1>>
  swap(const std::shared_ptr<Prod<T1, T2>> &p) {
    const auto &[d_a0, d_a1] = std::get<typename Prod<T1, T2>::Pair>(p->v());
    return Prod<T2, T1>::pair(d_a1, d_a0);
  }

  static inline const std::shared_ptr<
      Prod<std::shared_ptr<Nat>, std::shared_ptr<Nat>>>
      test_pair = make_pair<std::shared_ptr<Nat>, std::shared_ptr<Nat>>(
          Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())));
  static inline const std::shared_ptr<Nat> test_fst =
      fst<std::shared_ptr<Nat>, std::shared_ptr<Nat>>(test_pair);
  static inline const std::shared_ptr<
      Prod<std::shared_ptr<Nat>, std::shared_ptr<Nat>>>
      test_swap = swap<std::shared_ptr<Nat>, std::shared_ptr<Nat>>(test_pair);
};

#endif // INCLUDED_TUPLE
