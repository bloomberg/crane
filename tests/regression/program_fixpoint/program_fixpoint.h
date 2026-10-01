#ifndef INCLUDED_PROGRAM_FIXPOINT
#define INCLUDED_PROGRAM_FIXPOINT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A> struct Sig;
template <typename A, typename P> struct SigT;

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

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename _U> operator Sig<_U>() const {
    return {[&]() -> _U {
      if constexpr (crane_convertible<_U, const A &>) {
        return crane_convert<_U>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (crane_convertible<_U0, const A &>) {
                return crane_convert<_U0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const P &>) {
                return crane_convert<_U1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }

  P projT2() const {
    const auto &[x0, a1] = *this;
    return a1;
  }
};

struct ProgFix {
  static List<uint64_t>
  interleave_func(const SigT<List<uint64_t>, List<uint64_t>> &x);
  static List<uint64_t> interleave(const List<uint64_t> &l1,
                                   const List<uint64_t> &l2);
  static inline const List<uint64_t> test_interleave = interleave(
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()))),
      List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(4),
              List<uint64_t>::cons(UINT64_C(6), List<uint64_t>::nil()))));
};

#endif // INCLUDED_PROGRAM_FIXPOINT
