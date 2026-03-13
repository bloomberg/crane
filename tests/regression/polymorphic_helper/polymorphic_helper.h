#ifndef INCLUDED_POLYMORPHIC_HELPER
#define INCLUDED_POLYMORPHIC_HELPER

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

  std::shared_ptr<Nat> add(std::shared_ptr<Nat> m) const {
    return std::visit(
        Overloaded{[&](const typename Nat::O _args) -> std::shared_ptr<Nat> {
                     return m;
                   },
                   [&](const typename Nat::S _args) -> std::shared_ptr<Nat> {
                     std::shared_ptr<Nat> p = _args.d_a0;
                     return Nat::ctor::S_(std::move(p)->add(m));
                   }},
        this->v());
  }
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<Nat> length() const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args) -> std::shared_ptr<Nat> {
              return Nat::ctor::O_();
            },
            [](const typename List<t_A>::Cons _args) -> std::shared_ptr<Nat> {
              std::shared_ptr<List<t_A>> l_ = _args.d_a1;
              return Nat::ctor::S_(std::move(l_)->length());
            }},
        this->v());
  }
};

struct ListDef {
  template <typename T1>
  static std::shared_ptr<List<T1>> repeat(const T1 x,
                                          const std::shared_ptr<Nat> &n);
};

template <typename T1>
std::shared_ptr<Nat> _foo_aux(const T1 a, const std::shared_ptr<Nat> &n) {
  return ListDef::template repeat<T1>(a, n)->length();
}

std::shared_ptr<Nat> foo(std::shared_ptr<Nat> n, const bool b);

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x,
                                          const std::shared_ptr<Nat> &n) {
  return std::visit(
      Overloaded{[](const typename Nat::O _args) -> std::shared_ptr<List<T1>> {
                   return List<T1>::ctor::Nil_();
                 },
                 [&](const typename Nat::S _args) -> std::shared_ptr<List<T1>> {
                   std::shared_ptr<Nat> k = _args.d_a0;
                   return List<T1>::ctor::Cons_(
                       x, ListDef::template repeat<T1>(x, std::move(k)));
                 }},
      n->v());
}

#endif // INCLUDED_POLYMORPHIC_HELPER
