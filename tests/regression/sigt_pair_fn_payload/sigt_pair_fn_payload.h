#ifndef INCLUDED_SIGT_PAIR_FN_PAYLOAD
#define INCLUDED_SIGT_PAIR_FN_PAYLOAD

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

/// A sigT whose payload is a pair of a value and a function: both pair
/// components are boxed at the producer -- the function through the
/// erased-callable adapter -- so the consumer recovers the pair with a single
/// any_cast<pair<any,any>> and applies the callable.
struct SigtPairFnPayload {
  using item = SigT<std::any, std::pair<std::any, std::any>>;

  template <typename T1, typename F1> static item mk(T1 a, F1 &&f) {
    return SigT<std::any, std::pair<std::any, std::any>>::existt(
        std::any(), std::make_pair(std::any(a), std::any(crane_erase_fn(f))));
  }

  static inline const List<item> items =
      List<SigT<std::any, std::pair<std::any, std::any>>>::cons(
          mk<uint64_t>(UINT64_C(3), [](uint64_t n) { return n; }),
          List<SigT<std::any, std::pair<std::any, std::any>>>::cons(
              mk<bool>(true,
                       [](bool b) {
                         if (b) {
                           return UINT64_C(1);
                         } else {
                           return UINT64_C(0);
                         }
                       }),
              List<SigT<std::any, std::pair<std::any, std::any>>>::nil()));
  static uint64_t
  score(const SigT<std::any, std::pair<std::any, std::any>> &it);
  static inline const uint64_t go = items.template fold_left<uint64_t>(
      [](uint64_t acc, const auto &it) { return (acc + score(it)); },
      UINT64_C(0));
};

#endif // INCLUDED_SIGT_PAIR_FN_PAYLOAD
