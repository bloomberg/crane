#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct LoopifyOption {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const list<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename list<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a, l] =
                  std::get<typename list<CraneU>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (l ? std::make_shared<list<A>>(crane_convert<list<A>>(*l))
                     : nullptr)};
            }
          }()) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a, crane::shared_child_slot<list<A>> l) {
      return list<A>(Cons{std::move(a), l.take()});
    }

    // MANIPULATORS
    ~list() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    // Explicit stack replaces the non-tail recursion of list_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const list<T1> *l;
    };

    struct _after_list_rect_in_Cons {
      T1 a0;
      std::shared_ptr<list<T1>> a1;
    };

    using _frame = std::variant<_call, _after_list_rect_in_Cons>;
    T2 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_after_list_rect_in_Cons{a0, a1});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_list_rect_in_Cons>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        std::shared_ptr<list<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2 list_rec(T2 f, F1 &&f0, const list<T1> &l) {
    return list_rect<T1, T2>(std::move(f), f0, l);
  }

  /// find_opt p l returns the first element satisfying p, or None.
  template <typename T1, typename F0>
  static std::optional<T1> find_opt(F0 &&p, const list<T1> &l) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  /// last_opt l returns the last element, or None for empty.
  template <typename T1> static std::optional<T1> last_opt(const list<T1> &l) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename list<T1>::Nil>(_sv.v())) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  /// nth_opt n l returns the nth element, or None for out of bounds.
  template <typename T1>
  static std::optional<T1> nth_opt(uint64_t n, const list<T1> &l) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const list<T1> *_loop_l = &l;
    uint64_t _loop_n = n;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (_loop_n == UINT64_C(0)) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = crane_raw(a1);
          _loop_n =
              (((_loop_n - UINT64_C(1)) > _loop_n ? 0
                                                  : (_loop_n - UINT64_C(1))));
        }
      }
    }
  }

  /// lookup_opt key l looks up key in an association list.
  static std::optional<uint64_t>
  lookup_opt(uint64_t key, const list<std::pair<uint64_t, uint64_t>> &l);

  /// map_opt f l applies f and keeps only Some results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<std::optional<T2>, F0 &, const T1 &>
  static list<T2> map_opt(F0 &&f, const list<T1> &l) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<list<T2>> _root{};
    std::shared_ptr<list<T2>> *_write = nullptr;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        auto _value = list<T2>::nil();
        (_write ? *(*_write = std::make_shared<list<T2>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        auto _cs = f(a0);
        if (_cs.has_value()) {
          const T2 &y = *_cs;
          auto _cell = typename list<T2>::Cons(y, nullptr);
          list<T2> &_node = (
              _write ? *(*_write = std::make_shared<list<T2>>(std::move(_cell)))
                     : _root.emplace(std::move(_cell)));
          _write = &std::get<typename list<T2>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// find_index p l returns the index of the first match, or None.
  template <typename T1, typename F0>
  static std::optional<uint64_t> find_index_aux(F0 &&p, const list<T1> &l,
                                                uint64_t i) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    uint64_t _loop_i = i;
    const list<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<uint64_t>(_loop_i);
        } else {
          _loop_i = (_loop_i + 1);
          _loop_l = crane_raw(a1);
        }
      }
    }
  }

  template <typename T1, typename F0>
  static std::optional<uint64_t> find_index(F0 &&p, const list<T1> &l) {
    return find_index_aux<T1>(p, l, UINT64_C(0));
  }
};
