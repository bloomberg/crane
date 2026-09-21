#ifndef INCLUDED_ROCQ_BUG_16288
#define INCLUDED_ROCQ_BUG_16288

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
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
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (std::is_same_v<_U, std::any>) {
                   return crane_any_cast<A>(a);
                 } else {
                   if constexpr (std::is_constructible_v<A, const _U &>) {
                     return A(a);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
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
};

template <typename M>
concept Nop = true;

struct RocqBug16288 {
  struct Empty {};

  template <Nop N> struct M {
    template <typename elt> struct M_t_NonEmpty {
      List<elt> M_m;

      // ACCESSORS
      template <typename _U> operator M_t_NonEmpty<_U>() const {
        return {crane_convert<List<_U>>(M_m)};
      }
    };

    template <typename X, typename Y> struct M_t_NonEmpty_ {
      X a;
      Y b;

      // ACCESSORS
      template <typename _U0, typename _U1>
      operator M_t_NonEmpty_<_U0, _U1>() const {
        return {
            [&]() -> _U0 {
              if constexpr (std::is_same_v<X, std::any>) {
                return crane_any_cast<_U0>(a);
              } else {
                if constexpr (std::is_constructible_v<_U0, const X &>) {
                  return _U0(a);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }(),
            [&]() -> _U1 {
              if constexpr (std::is_same_v<Y, std::any>) {
                return crane_any_cast<_U1>(b);
              } else {
                if constexpr (std::is_constructible_v<_U1, const Y &>) {
                  return _U1(b);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }()};
      }
    };
  };

  using M_ = M<Empty>;
};

#endif // INCLUDED_ROCQ_BUG_16288
