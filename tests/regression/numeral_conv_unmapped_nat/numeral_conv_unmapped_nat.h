#ifndef INCLUDED_NUMERAL_CONV_UNMAPPED_NAT
#define INCLUDED_NUMERAL_CONV_UNMAPPED_NAT

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
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

/// ZInt maps Z to int64_t but leaves nat as the extracted unary
/// inductive, so Z.of_nat 2 becomes static_cast<int64_t>(Nat::s(Nat::s(
/// Nat::o()))) -- a cast from a struct with no conversion operator.  The
/// converter is folded to a cast without checking that its argument was folded
/// to a literal too.
struct NumeralConvUnmappedNat {
  static inline const List<int64_t> xs = List<int64_t>::cons(
      INT64_C(-5),
      List<int64_t>::cons(
          INT64_C(3), List<int64_t>::cons(
                          INT64_C(0), List<int64_t>::cons(
                                          INT64_C(7), List<int64_t>::nil()))));
  static inline const int64_t run = static_cast<int64_t>(
      static_cast<uint64_t>(static_cast<int64_t>(
          static_cast<uint64_t>(xs.template fold_left<int64_t>(
              [](int64_t _x0, int64_t _x1) -> int64_t {
                return static_cast<int64_t>(static_cast<uint64_t>(_x0) +
                                            static_cast<uint64_t>(_x1));
              },
              INT64_C(0))) +
          static_cast<uint64_t>(
              (INT64_C(-9) < 0
                   ? static_cast<int64_t>(-static_cast<uint64_t>(INT64_C(-9)))
                   : INT64_C(-9))))) +
      static_cast<uint64_t>(static_cast<int64_t>(UINT64_C(2))));
};

#endif // INCLUDED_NUMERAL_CONV_UNMAPPED_NAT
