#ifndef INCLUDED_HKT_CLASS_PARAM
#define INCLUDED_HKT_CLASS_PARAM

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<std::any>> l;
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
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<std::any> l) {
    return List<A>(
        Cons{std::move(a), std::make_shared<List<std::any>>(std::move(l))});
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
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return crane_call_erased(f, std::any_cast<A>(a1),
                               a2->template fold_right<T1>(f, a0));
    }
  }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

/// A type class parameterised over a type {i constructor} (C : Type -> Type).
/// Crane emits the instance's methods against the shared List type but
/// erases the element type, producing List<std::any> parameters where
/// List<Nat> is required, which corrupts the mapped List type itself.
template <typename I>
concept Container = requires {
  typename I::C;
  { I::empty() } -> std::convertible_to<typename I::C>;
  {
    I::insert(std::declval<std::any>(), std::declval<typename I::C>())
  } -> std::convertible_to<typename I::C>;
  {
    I::toList(std::declval<typename I::C>())
  } -> std::convertible_to<List<std::any>>;
};

struct HktClassParam {
  template <Container _tcI0> static typename _tcI0::C empty() {
    return crane_any_cast<typename _tcI0::C>(_tcI0::empty());
  }

  template <Container _tcI0, typename T2>
  static typename _tcI0::C insert(const T2 &x, const typename _tcI0::C &x0) {
    return crane_any_cast<typename _tcI0::C>(_tcI0::insert(x, x0));
  }

  template <Container _tcI0>
  static List<std::any> toList(const typename _tcI0::C &x) {
    return _tcI0::toList(x);
  }

  struct ListContainer {
    using C = List<std::any>;

    static List<std::any> empty() { return List<std::any>::nil(); }

    static List<std::any> insert(std::any x, List<std::any> xs) {
      return List<std::any>::cons(x, xs);
    }

    static List<std::any> toList(List<std::any> xs) { return xs; }
  };

  static_assert(Container<ListContainer>);

  template <Container _tcI0>
  static typename _tcI0::C build(const List<std::any> &l) {
    return l.template fold_right<typename _tcI0::C>(
        [](uint64_t n, const typename _tcI0::C &acc) {
          return insert<_tcI0, uint64_t>(n, acc);
        },
        empty<_tcI0>());
  }

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_HKT_CLASS_PARAM
