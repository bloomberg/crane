#ifndef INCLUDED_BIND_TYPE_INFERENCE
#define INCLUDED_BIND_TYPE_INFERENCE

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class Unit { e_TT };

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
};

struct BindTypeInference {
  template <typename T1>
  __attribute__((pure)) static T1 ignoreAndReturn(const T1 b) {
    Unit _x = Unit::e_TT;
    return b;
  }

  __attribute__((pure)) static int64_t test1();

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  __attribute__((pure)) static T2 transform(const T1 ma, F1 &&f) {
    T1 x = ma;
    return f(x);
  }

  __attribute__((pure)) static int64_t test2();

  template <typename T1, typename T2, typename T3, typename F1, typename F2>
  __attribute__((pure)) static T3 nested(const T1 a, F1 &&f, F2 &&g) {
    T1 x = a;
    T2 y = f(x);
    return g(y);
  }

  __attribute__((pure)) static int64_t test3();
  __attribute__((pure)) static int64_t test4();
  static std::shared_ptr<List<int64_t>> intToList(const int64_t n);
  __attribute__((pure)) static std::shared_ptr<List<int64_t>> test5();
  __attribute__((pure)) static int64_t test6();
};

#endif // INCLUDED_BIND_TYPE_INFERENCE
