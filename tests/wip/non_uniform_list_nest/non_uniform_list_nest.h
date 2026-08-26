#ifndef INCLUDED_NON_UNIFORM_LIST_NEST
#define INCLUDED_NON_UNIFORM_LIST_NEST

#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

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
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
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

struct NonUniformListNest {
  template <typename A> struct n2 {
    // TYPES
    struct Z2 {
      A a0;
    };

    struct S2 {
      std::shared_ptr<n2<List<A>>> a0;
    };

    using variant_t = std::variant<Z2, S2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    n2() {}

    explicit n2(Z2 _v) : v_(std::move(_v)) {}

    explicit n2(S2 _v) : v_(std::move(_v)) {}

    template <typename _U> n2(const n2<_U> &_other) {
      if (std::holds_alternative<typename n2<_U>::Z2>(_other.v())) {
        const auto &[a0] = std::get<typename n2<_U>::Z2>(_other.v());
        this->v_ = Z2{[&]() -> A {
          if constexpr (std::is_same_v<_U, std::any>) {
            if (a0.type() == typeid(A))
              return std::any_cast<A>(a0);
            if constexpr (requires {
                            typename A::first_type;
                            typename A::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
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
            return std::any_cast<A>(a0);
          } else
            return A(a0);
        }()};
      } else {
        const auto &[a0] = std::get<typename n2<_U>::S2>(_other.v());
        this->v_ = S2{a0 ? std::make_shared<n2<List<A>>>(*a0) : nullptr};
      }
    }

    static n2<A> z2(A a0) { return n2(Z2{std::move(a0)}); }

    static n2<A> s2(n2<List<A>> a0) {
      return n2(S2{std::make_shared<n2<List<A>>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1>
  static T1 n2_rect(F0 &&f, F1 &&f0, const n2<T2> &n) {
    if (std::holds_alternative<typename n2<T2>::Z2>(n.v())) {
      const auto &[a0] = std::get<typename n2<T2>::Z2>(n.v());
      return std::any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename n2<T2>::S2>(n.v());
      return std::any_cast<T1>(f0(*a0, n2_rect<T1, T2>(f, f0, *a0)));
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
  static T1 n2_rec(F0 &&f, F1 &&f0, const n2<T2> &n) {
    if (std::holds_alternative<typename n2<T2>::Z2>(n.v())) {
      const auto &[a0] = std::get<typename n2<T2>::Z2>(n.v());
      return std::any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename n2<T2>::S2>(n.v());
      return std::any_cast<T1>(f0(*a0, n2_rec<T1, T2>(f, f0, *a0)));
    }
  }

  template <typename T1> static uint64_t depth(const n2<T1> &x) {
    if (std::holds_alternative<typename n2<T1>::Z2>(x.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0] = std::get<typename n2<T1>::S2>(x.v());
      return (depth<T1>(*a0) + 1);
    }
  }

  static inline const uint64_t go =
      depth<uint64_t>(n2<uint64_t>::s2(n2<List<uint64_t>>::z2(
          List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()))));
};

#endif // INCLUDED_NON_UNIFORM_LIST_NEST
