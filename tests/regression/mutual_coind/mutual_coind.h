#ifndef INCLUDED_MUTUAL_COIND
#define INCLUDED_MUTUAL_COIND

#include "lazy.h"
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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
};

struct MutualCoind {
  template <typename t_A> struct streamA;
  template <typename t_A> struct streamB;

  template <typename t_A> struct streamA {
    // TYPES
    struct ConsA {
      t_A d_a0;
      std::shared_ptr<streamB<t_A>> d_a1;
    };

    using variant_t = std::variant<ConsA>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit streamA(ConsA _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit streamA(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static std::shared_ptr<streamA<t_A>>
    consa(t_A a0, const std::shared_ptr<streamB<t_A>> &a1) {
      return std::make_shared<streamA<t_A>>(ConsA{std::move(a0), a1});
    }

    static std::shared_ptr<streamA<t_A>>
    consa(t_A a0, std::shared_ptr<streamB<t_A>> &&a1) {
      return std::make_shared<streamA<t_A>>(
          ConsA{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<streamA<t_A>>
    lazy_(std::function<std::shared_ptr<streamA<t_A>>()> thunk) {
      return std::make_shared<streamA<t_A>>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            std::shared_ptr<streamA<t_A>> _tmp = thunk();
            return _tmp->v();
          }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename t_A> struct streamB {
    // TYPES
    struct ConsB {
      t_A d_a0;
      std::shared_ptr<streamA<t_A>> d_a1;
    };

    using variant_t = std::variant<ConsB>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit streamB(ConsB _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit streamB(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static std::shared_ptr<streamB<t_A>>
    consb(t_A a0, const std::shared_ptr<streamA<t_A>> &a1) {
      return std::make_shared<streamB<t_A>>(ConsB{std::move(a0), a1});
    }

    static std::shared_ptr<streamB<t_A>>
    consb(t_A a0, std::shared_ptr<streamA<t_A>> &&a1) {
      return std::make_shared<streamB<t_A>>(
          ConsB{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<streamB<t_A>>
    lazy_(std::function<std::shared_ptr<streamB<t_A>>()> thunk) {
      return std::make_shared<streamB<t_A>>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            std::shared_ptr<streamB<t_A>> _tmp = thunk();
            return _tmp->v();
          }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename T1>
  static T1 headA(const std::shared_ptr<streamA<T1>> &s) {
    return std::visit(
        Overloaded{[](const typename streamA<T1>::ConsA &_args) -> T1 {
          return _args.d_a0;
        }},
        s->v());
  }

  template <typename T1>
  static std::shared_ptr<streamB<T1>>
  tailA(const std::shared_ptr<streamA<T1>> &s) {
    return streamB<T1>::lazy_([=]() mutable -> std::shared_ptr<streamB<T1>> {
      return std::visit(Overloaded{[](const typename streamA<T1>::ConsA &_args)
                                       -> std::shared_ptr<streamB<T1>> {
                          return _args.d_a1;
                        }},
                        s->v());
    });
  }

  template <typename T1>
  static T1 headB(const std::shared_ptr<streamB<T1>> &s) {
    return std::visit(
        Overloaded{[](const typename streamB<T1>::ConsB &_args) -> T1 {
          return _args.d_a0;
        }},
        s->v());
  }

  template <typename T1>
  static std::shared_ptr<streamA<T1>>
  tailB(const std::shared_ptr<streamB<T1>> &s) {
    return streamA<T1>::lazy_([=]() mutable -> std::shared_ptr<streamA<T1>> {
      return std::visit(Overloaded{[](const typename streamB<T1>::ConsB &_args)
                                       -> std::shared_ptr<streamA<T1>> {
                          return _args.d_a1;
                        }},
                        s->v());
    });
  }

  static std::shared_ptr<streamA<unsigned int>> countA(const unsigned int n);
  static std::shared_ptr<streamB<unsigned int>> countB(const unsigned int n);

  template <typename T1>
  static std::shared_ptr<List<T1>>
  takeA(const unsigned int fuel, const std::shared_ptr<streamA<T1>> &s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int f = fuel - 1;
      return std::visit(Overloaded{[&](const typename streamA<T1>::ConsA &_args)
                                       -> std::shared_ptr<List<T1>> {
                          return List<T1>::cons(_args.d_a0,
                                                takeB<T1>(f, _args.d_a1));
                        }},
                        s->v());
    }
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  takeB(const unsigned int fuel, const std::shared_ptr<streamB<T1>> &s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int f = fuel - 1;
      return std::visit(Overloaded{[&](const typename streamB<T1>::ConsB &_args)
                                       -> std::shared_ptr<List<T1>> {
                          return List<T1>::cons(_args.d_a0,
                                                takeA<T1>(f, _args.d_a1));
                        }},
                        s->v());
    }
  }

  static inline const unsigned int test_headA = headA<unsigned int>(countA(0u));
  static inline const unsigned int test_headB =
      headB<unsigned int>(countB(10u));
  static inline const std::shared_ptr<List<unsigned int>> test_take5 =
      takeA<unsigned int>(5u, countA(0u));
};

#endif // INCLUDED_MUTUAL_COIND
