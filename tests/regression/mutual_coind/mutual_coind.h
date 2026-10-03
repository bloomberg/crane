#ifndef INCLUDED_MUTUAL_COIND
#define INCLUDED_MUTUAL_COIND

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct MutualCoind {
  template <typename A> struct streamA;
  template <typename A> struct streamB;

  template <typename A> struct streamA {
    // TYPES
    template <typename _S0 = streamA<A>, typename _S1 = streamB<A>>
    struct ConsA_ {
      A a0;
      _S1 a1;
    };

    using ConsA = ConsA_<>;
    using variant_t = std::variant<ConsA>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    streamA() {}

    explicit streamA(ConsA _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename _U>
    streamA(const streamA<_U> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                const auto &[a0, a1] =
                    std::get<typename streamA<_U>::ConsA>(_other.v());
                return ConsA{[&]() -> A {
                               if constexpr (crane_convertible<A, const _U &>) {
                                 return crane_convert<A>(a0);
                               } else {
                                 throw std::logic_error(
                                     "unreachable: inactive constructor field "
                                     "at this instantiation");
                               }
                             }(),
                             crane_convert<streamB<A>>(a1)};
              })) {}

    explicit streamA(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static streamA<A> consa(A a0, streamB<A> a1) {
      return streamA<A>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, std::move(a0), std::move(a1)));
    }

    explicit streamA(crane::lazy<variant_t> _cell)
        : lazy_v_(std::move(_cell)) {}

    template <typename F> static streamA<A> lazy_(F &&thunk) {
      return streamA<A>(
          crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename A> struct streamB {
    // TYPES
    template <typename _S0 = streamB<A>, typename _S1 = streamA<A>>
    struct ConsB_ {
      A a0;
      _S1 a1;
    };

    using ConsB = ConsB_<>;
    using variant_t = std::variant<ConsB>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    streamB() {}

    explicit streamB(ConsB _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename _U>
    streamB(const streamB<_U> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                const auto &[a0, a1] =
                    std::get<typename streamB<_U>::ConsB>(_other.v());
                return ConsB{[&]() -> A {
                               if constexpr (crane_convertible<A, const _U &>) {
                                 return crane_convert<A>(a0);
                               } else {
                                 throw std::logic_error(
                                     "unreachable: inactive constructor field "
                                     "at this instantiation");
                               }
                             }(),
                             crane_convert<streamA<A>>(a1)};
              })) {}

    explicit streamB(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static streamB<A> consb(A a0, streamA<A> a1) {
      return streamB<A>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, std::move(a0), std::move(a1)));
    }

    explicit streamB(crane::lazy<variant_t> _cell)
        : lazy_v_(std::move(_cell)) {}

    template <typename F> static streamB<A> lazy_(F &&thunk) {
      return streamB<A>(
          crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename T1> static T1 headA(streamA<T1> s) {
    const auto &[a0, a1] = std::get<typename streamA<T1>::ConsA>(s.v());
    return a0;
  }

  template <typename T1> static streamB<T1> tailA(streamA<T1> s) {
    const auto &[a0, a1] = std::get<typename streamA<T1>::ConsA>(s.v());
    return a1;
  }

  template <typename T1> static T1 headB(streamB<T1> s) {
    const auto &[a0, a1] = std::get<typename streamB<T1>::ConsB>(s.v());
    return a0;
  }

  template <typename T1> static streamA<T1> tailB(streamB<T1> s) {
    const auto &[a0, a1] = std::get<typename streamB<T1>::ConsB>(s.v());
    return a1;
  }

  static streamA<uint64_t> countA(uint64_t n);
  static streamB<uint64_t> countB(uint64_t n);

  template <typename T1> static List<T1> takeA(uint64_t fuel, streamA<T1> s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t f = fuel - 1;
      const auto &[a0, a1] = std::get<typename streamA<T1>::ConsA>(s.v());
      return List<T1>::cons(a0, takeB<T1>(f, a1));
    }
  }

  template <typename T1> static List<T1> takeB(uint64_t fuel, streamB<T1> s) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t f = fuel - 1;
      const auto &[a0, a1] = std::get<typename streamB<T1>::ConsB>(s.v());
      return List<T1>::cons(a0, takeA<T1>(f, a1));
    }
  }

  static inline const uint64_t test_headA =
      headA<uint64_t>(countA(UINT64_C(0)));
  static inline const uint64_t test_headB =
      headB<uint64_t>(countB(UINT64_C(10)));
  static inline const List<uint64_t> test_take5 =
      takeA<uint64_t>(UINT64_C(5), countA(UINT64_C(0)));
};

#endif // INCLUDED_MUTUAL_COIND
