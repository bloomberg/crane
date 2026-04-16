#ifndef INCLUDED_POLYMORPHIC_HELPER
#define INCLUDED_POLYMORPHIC_HELPER

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

  std::shared_ptr<Nat> add(std::shared_ptr<Nat> m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(this->v());
      return Nat::s(d_a0->add(m));
    }
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<Nat> length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return Nat::o();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return Nat::s(d_a1->length());
    }
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
  if (std::holds_alternative<typename Nat::O>(n->v())) {
    return List<T1>::nil();
  } else {
    const auto &[d_a0] = std::get<typename Nat::S>(n->v());
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, d_a0));
  }
}

#endif // INCLUDED_POLYMORPHIC_HELPER
