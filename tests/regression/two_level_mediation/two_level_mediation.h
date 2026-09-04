#ifndef INCLUDED_TWO_LEVEL_MEDIATION
#define INCLUDED_TWO_LEVEL_MEDIATION

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
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
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(a);
                        else
                          return A(a);
                      }(),
                      l ? std::make_shared<List<A>>(*l) : nullptr};
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

struct TwoLevelMediation {
  template <typename A> struct w {
    // DATA
    uint64_t a0;
    List<A> a1;

    // ACCESSORS
    w<A> clone() const { return {a0, a1}; }

    // CREATORS
    static w<A> mkw(uint64_t a0, List<A> a1) { return {a0, std::move(a1)}; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<A> &>
    T1 w_rec(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<A> &>
    T1 w_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  struct t {
    // TYPES
    struct Node {
      std::shared_ptr<w<t>> a0;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Node _v) : v_(std::move(_v)) {}

    static t node(w<t> a0) {
      return t(Node{std::make_shared<w<t>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            crane::small_vector<std::shared_ptr<List<t>>> _hw1;
            if (auto *_ha5 = std::get_if<typename List<t>::Cons>(
                    &_alt->a0->a1.v_mut())) {
              _stack.push_back(std::make_shared<t>(std::move(_ha5->a)));
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
                      std::get_if<typename List<t>::Cons>(&_hw1e.v_mut())) {
                _stack.push_back(std::make_shared<t>(std::move(_ha3->a)));
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

    t wrap(uint64_t k) const {
      return t::node(
          w<t>::mkw(k, List<t>::cons(std::move(*this), List<t>::nil())));
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, w<t> &>
    T1 t_rec(F0 &&f) const {
      const auto &[a0] = std::get<typename t::Node>(this->v());
      return f(*a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, w<t> &>
    T1 t_rect(F0 &&f) const {
      const auto &[a0] = std::get<typename t::Node>(this->v());
      return f(*a0);
    }
  };

  static inline const t empty = t::node(w<t>::mkw(UINT64_C(0), List<t>::nil()));
};

#endif // INCLUDED_TWO_LEVEL_MEDIATION
