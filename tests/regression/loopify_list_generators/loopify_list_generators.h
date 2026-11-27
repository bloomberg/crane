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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (_result + 1);
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct LoopifyListGenerators {
  static List<uint64_t> cycle_fuel(uint64_t fuel, uint64_t n,
                                   const List<uint64_t> &l);
  static List<uint64_t> cycle(uint64_t n, const List<uint64_t> &l);

  template <typename F0>
  static List<uint64_t> iterate(F0 &&f, uint64_t n, uint64_t x) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    while (true) {
      if (n <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t n_ = n - 1;
        auto _cell = typename List<uint64_t>::Cons(x, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        x = f(x);
        n = n_;
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename F2>
  static List<uint64_t> build_list_aux(uint64_t n, uint64_t idx, F2 &&f) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    while (true) {
      if (n <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t n_ = n - 1;
        auto _cell = typename List<uint64_t>::Cons(f(idx), nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        idx = idx + UINT64_C(1);
        n = n_;
        continue;
      }
    }
    return std::move(*_root);
  }

  template <typename F1> static List<uint64_t> build_list(uint64_t n, F1 &&f) {
    return build_list_aux(n, UINT64_C(0), f);
  }

  template <typename F1> static List<uint64_t> init_list(uint64_t n, F1 &&f) {
    if (n <= 0) {
      return List<uint64_t>::nil();
    } else {
      uint64_t n_ = n - 1;
      return List<uint64_t>::cons(f(UINT64_C(0)), [&]() {
        auto go = [&](uint64_t i) -> List<uint64_t> {
          // Explicit stack replaces the non-tail recursion of go: _call frames
          // are pending calls, _after frames resume a caller.
          struct _call {
            uint64_t i;
          };

          struct _after_go_in_S {
            uint64_t i;
          };

          using _frame = std::variant<_call, _after_go_in_S>;
          List<uint64_t> _result{};
          crane::small_vector<_frame> _stack;
          _stack.emplace_back(_call{i});
          while (!_stack.empty()) {
            _frame &_popped = _stack.back();
            if (std::holds_alternative<_call>(_popped)) {
              auto _f = std::move(std::get<_call>(_popped));
              _stack.pop_back();
              uint64_t i = _f.i;
              if (i <= 0) {
                _result = List<uint64_t>::nil();
              } else {
                uint64_t i_ = i - 1;
                _stack.emplace_back(_after_go_in_S{i});
                _stack.emplace_back(_call{i_});
              }
            } else {
              auto _f = std::move(std::get<_after_go_in_S>(_popped));
              _stack.pop_back();
              uint64_t i = _f.i;
              _result = List<uint64_t>::cons(f((n - i > n ? 0 : n - i)),
                                             std::move(_result));
            }
          }
          return _result;
        };
        return go(n_);
      }());
    }
  }

  static List<uint64_t> range(uint64_t start, uint64_t count);
  static List<uint64_t> replicate_elem(uint64_t n, uint64_t x);
  static List<uint64_t> replicate_each(uint64_t n, const List<uint64_t> &l);

  template <typename F1> static List<uint64_t> tabulate(uint64_t n, F1 &&f) {
    if (n <= 0) {
      return List<uint64_t>::nil();
    } else {
      uint64_t n_ =
          n -
          1; // Explicit stack replaces the non-tail recursion of aux: _call frames are pending calls, _after frames resume a caller.

      struct _call {
        uint64_t idx;
      };

      struct _after_aux_in_S {
        uint64_t idx;
      };

      using _frame = std::variant<_call, _after_aux_in_S>;
      List<uint64_t> _lc1_result{};
      crane::small_vector<_frame> _lc1_stack;
      _lc1_stack.emplace_back(_call{n_});
      while (!_lc1_stack.empty()) {
        _frame &_popped = _lc1_stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _lc1_stack.pop_back();
          uint64_t n_ = _f.idx;
          if (n_ <= 0) {
            _lc1_result =
                List<uint64_t>::cons(f(UINT64_C(0)), List<uint64_t>::nil());
          } else {
            uint64_t idx_ = n_ - 1;
            _lc1_stack.emplace_back(_after_aux_in_S{n_});
            _lc1_stack.emplace_back(_call{idx_});
          }
        } else {
          auto _f = std::move(std::get<_after_aux_in_S>(_popped));
          _lc1_stack.pop_back();
          uint64_t n_ = _f.idx;
          _lc1_result = _lc1_result.app(
              List<uint64_t>::cons(f(n_), List<uint64_t>::nil()));
        }
      }
      return _lc1_result;
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &,
                                   const uint64_t &>
  static List<uint64_t> zip_with(F0 &&f, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l2 = &l2;
    const List<uint64_t> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
          auto _value = List<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
          auto _cell = typename List<uint64_t>::Cons(f(a0, a00), nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  static List<std::pair<uint64_t, uint64_t>>
  enumerate_aux(uint64_t idx, const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>> enumerate(const List<uint64_t> &l);
};
