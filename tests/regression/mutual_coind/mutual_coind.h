#ifndef INCLUDED_MUTUAL_COIND
#define INCLUDED_MUTUAL_COIND

#include "lazy.h"
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

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
    using crane_element_type = t_A;

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
    consa(t_A a0, std::shared_ptr<streamB<t_A>> a1) {
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
    using crane_element_type = t_A;

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
    consb(t_A a0, std::shared_ptr<streamA<t_A>> a1) {
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
    const auto &[d_a0, d_a1] = std::get<typename streamA<T1>::ConsA>(s->v());
    return d_a0;
  }

  template <typename T1>
  static std::shared_ptr<streamB<T1>>
  tailA(const std::shared_ptr<streamA<T1>> &s) {
    const auto &[d_a0, d_a1] = std::get<typename streamA<T1>::ConsA>(s->v());
    return streamB<T1>::lazy_(
        [=]() mutable -> std::shared_ptr<streamB<T1>> { return d_a1; });
  }

  template <typename T1>
  static T1 headB(const std::shared_ptr<streamB<T1>> &s) {
    const auto &[d_a0, d_a1] = std::get<typename streamB<T1>::ConsB>(s->v());
    return d_a0;
  }

  template <typename T1>
  static std::shared_ptr<streamA<T1>>
  tailB(const std::shared_ptr<streamB<T1>> &s) {
    const auto &[d_a0, d_a1] = std::get<typename streamB<T1>::ConsB>(s->v());
    return streamA<T1>::lazy_(
        [=]() mutable -> std::shared_ptr<streamA<T1>> { return d_a1; });
  }

  static std::shared_ptr<streamA<unsigned int>> countA(unsigned int n);
  static std::shared_ptr<streamB<unsigned int>> countB(unsigned int n);

  template <typename T1>
  __attribute__((pure)) static List<T1>
  takeA(const unsigned int &fuel, const std::shared_ptr<streamA<T1>> &s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int f = fuel - 1;
      const auto &[d_a0, d_a1] = std::get<typename streamA<T1>::ConsA>(s->v());
      return List<T1>::cons(d_a0, takeB<T1>(f, d_a1));
    }
  }

  template <typename T1>
  __attribute__((pure)) static List<T1>
  takeB(const unsigned int &fuel, const std::shared_ptr<streamB<T1>> &s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int f = fuel - 1;
      const auto &[d_a0, d_a1] = std::get<typename streamB<T1>::ConsB>(s->v());
      return List<T1>::cons(d_a0, takeA<T1>(f, d_a1));
    }
  }

  static inline const unsigned int test_headA = headA<unsigned int>(countA(0u));
  static inline const unsigned int test_headB =
      headB<unsigned int>(countB(10u));
  static inline const List<unsigned int> test_take5 =
      takeA<unsigned int>(5u, countA(0u));
};

#endif // INCLUDED_MUTUAL_COIND
