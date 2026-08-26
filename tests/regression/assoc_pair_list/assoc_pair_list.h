#ifndef INCLUDED_ASSOC_PAIR_LIST
#define INCLUDED_ASSOC_PAIR_LIST

#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return a2->template fold_left<T1>(f, f(a0, a1));
    }
  }
};

struct AssocPairList {
  struct t {
    // TYPES
    struct Node {
      std::shared_ptr<List<std::pair<uint64_t, t>>> a0;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Node _v) : v_(std::move(_v)) {}

    static t node(List<std::pair<uint64_t, t>> a0) {
      return t(
          Node{std::make_shared<List<std::pair<uint64_t, t>>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            crane::small_vector<std::shared_ptr<List<std::pair<uint64_t, t>>>>
                _hw1;
            if (auto *_ha5 =
                    std::get_if<typename List<std::pair<uint64_t, t>>::Cons>(
                        &((*(_alt->a0))).v_mut())) {
              _stack.push_back(
                  std::make_shared<t>(std::move((_ha5->a).second)));
              _hw1.push_back(std::move(_ha5->l));
            }
            while (!_hw1.empty()) {
              auto _hw1p = std::move(_hw1.back());
              _hw1.pop_back();
              if (!_hw1p || _hw1p.use_count() != 1) {
                continue;
              }
              std::atomic_thread_fence(std::memory_order_acquire);
              auto &_hw1e = *_hw1p;
              if (auto *_ha3 =
                      std::get_if<typename List<std::pair<uint64_t, t>>::Cons>(
                          &(_hw1e).v_mut())) {
                _stack.push_back(
                    std::make_shared<t>(std::move((_ha3->a).second)));
                _hw1.push_back(std::move(_ha3->l));
              }
            }
            _alt->a0.reset();
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) noexcept = default;
    t &operator=(t &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, List<std::pair<uint64_t, t>> &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[a0] = std::get<typename t::Node>(t0.v());
    return f(*a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, List<std::pair<uint64_t, t>> &>
  static T1 t_rec(F0 &&f, const t &t0) {
    const auto &[a0] = std::get<typename t::Node>(t0.v());
    return f(*a0);
  }

  static t wrap(uint64_t k, t acc);
  static inline const t empty = t::node(List<std::pair<uint64_t, t>>::nil());
  static uint64_t count(const t &x);
};

#endif // INCLUDED_ASSOC_PAIR_LIST
