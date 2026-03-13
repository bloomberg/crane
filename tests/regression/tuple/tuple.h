#ifndef INCLUDED_TUPLE
#define INCLUDED_TUPLE

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

  // CREATORS
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Nat> O_() {
      return std::shared_ptr<Nat>(new Nat(O{}));
    }

    static std::shared_ptr<Nat> S_(const std::shared_ptr<Nat> &a0) {
      return std::shared_ptr<Nat>(new Nat(S{a0}));
    }

    static std::unique_ptr<Nat> O_uptr() {
      return std::unique_ptr<Nat>(new Nat(O{}));
    }

    static std::unique_ptr<Nat> S_uptr(const std::shared_ptr<Nat> &a0) {
      return std::unique_ptr<Nat>(new Nat(S{a0}));
    }
  };

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

  // CREATORS
  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Prod<t_A, t_B>> Pair_(t_A a0, t_B a1) {
      return std::shared_ptr<Prod<t_A, t_B>>(new Prod<t_A, t_B>(Pair{a0, a1}));
    }

    static std::unique_ptr<Prod<t_A, t_B>> Pair_uptr(t_A a0, t_B a1) {
      return std::unique_ptr<Prod<t_A, t_B>>(new Prod<t_A, t_B>(Pair{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Tuple {
  template <typename a, typename b> using pair = std::shared_ptr<Prod<a, b>>;

  template <typename T1, typename T2>
  static std::shared_ptr<Prod<T1, T2>> make_pair(const T1 a, const T2 b) {
    return Prod<T1, T2>::ctor::Pair_(a, b);
  }

  template <typename T1, typename T2>
  static T1 fst(const std::shared_ptr<Prod<T1, T2>> &p) {
    return std::visit(
        Overloaded{[](const typename Prod<T1, T2>::Pair _args) -> T1 {
          T1 a = _args.d_a0;
          return a;
        }},
        p->v());
  }

  template <typename T1, typename T2>
  static T2 snd(const std::shared_ptr<Prod<T1, T2>> &p) {
    return std::visit(
        Overloaded{[](const typename Prod<T1, T2>::Pair _args) -> T2 {
          T2 b = _args.d_a1;
          return b;
        }},
        p->v());
  }

  template <typename T1, typename T2>
  static std::shared_ptr<Prod<T2, T1>>
  swap(const std::shared_ptr<Prod<T1, T2>> &p) {
    return std::visit(Overloaded{[](const typename Prod<T1, T2>::Pair _args)
                                     -> std::shared_ptr<Prod<T2, T1>> {
                        T1 a = _args.d_a0;
                        T2 b = _args.d_a1;
                        return Prod<T2, T1>::ctor::Pair_(b, a);
                      }},
                      p->v());
  }

  static inline const std::shared_ptr<
      Prod<std::shared_ptr<Nat>, std::shared_ptr<Nat>>>
      test_pair = make_pair<std::shared_ptr<Nat>, std::shared_ptr<Nat>>(
          Nat::ctor::S_(Nat::ctor::O_()),
          Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())));
  static inline const std::shared_ptr<Nat> test_fst =
      fst<std::shared_ptr<Nat>, std::shared_ptr<Nat>>(test_pair);
  static inline const std::shared_ptr<
      Prod<std::shared_ptr<Nat>, std::shared_ptr<Nat>>>
      test_swap = swap<std::shared_ptr<Nat>, std::shared_ptr<Nat>>(test_pair);
};

#endif // INCLUDED_TUPLE
