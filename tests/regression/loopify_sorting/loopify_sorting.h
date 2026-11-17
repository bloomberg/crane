#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
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

/// Consolidated UNIQUE sorting algorithms and related operations.
struct LoopifySorting {
  template <typename T1> static uint64_t len_impl(const List<T1> &l) {
    // Explicit stack replaces the non-tail recursion of len_impl: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<T1> *l;
    };

    struct _after_len_impl_in_Cons {};

    using _frame = std::variant<_call, _after_len_impl_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_after_len_impl_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_len_impl_in_Cons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  static List<uint64_t> insert(uint64_t x, const List<uint64_t> &l);
  static List<uint64_t> insertion_sort(const List<uint64_t> &l);

  template <typename T1>
  static std::pair<List<T1>, List<T1>> split(const List<T1> &l) {
    // Explicit stack replaces the non-tail recursion of split: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const List<T1> *l;
    };

    struct _after_split_in_Cons {
      T1 a0;
      T1 a00;
    };

    using _frame = std::variant<_call, _after_split_in_Cons>;
    std::pair<List<T1>, List<T1>> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
            _result = std::make_pair(List<T1>::cons(a0, List<T1>::nil()),
                                     List<T1>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<T1>::Cons>(_sv0.v());
            _stack.emplace_back(_after_split_in_Cons{a0, a00});
            _stack.emplace_back(_call{crane_raw(a10)});
          }
        }
      } else {
        auto _f = std::move(std::get<_after_split_in_Cons>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        auto a00 = std::move(_f.a00);
        auto [l1, l2] = std::move(_result);
        _result = std::make_pair(List<T1>::cons(std::move(a0), std::move(l1)),
                                 List<T1>::cons(std::move(a00), std::move(l2)));
      }
    }
    return _result;
  }

  static List<uint64_t> merge_fuel(uint64_t fuel, const List<uint64_t> &l1,
                                   const List<uint64_t> &l2);
  static List<uint64_t> merge(const List<uint64_t> &l1,
                              const List<uint64_t> &l2);
  static List<uint64_t> merge_sort_fuel(uint64_t fuel, const List<uint64_t> &l);
  static List<uint64_t> merge_sort(const List<uint64_t> &l);
  static std::pair<List<uint64_t>, List<uint64_t>>
  partition(uint64_t pivot, const List<uint64_t> &l);
  static List<uint64_t> quicksort_fuel(uint64_t fuel, const List<uint64_t> &l);
  static List<uint64_t> quicksort(const List<uint64_t> &l);
  static bool is_sorted_aux(uint64_t prev, const List<uint64_t> &l);
  static bool is_sorted(const List<uint64_t> &l);

  /// merge_by cmp merges with custom comparator.
  template <typename F1>
  static List<uint64_t> merge_by_fuel(uint64_t fuel, F1 &&cmp,
                                      const List<uint64_t> &l1,
                                      const List<uint64_t> &l2) {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l2 = &l2;
    const List<uint64_t> *_loop_l1 = &l1;
    uint64_t _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
          auto _value = *_loop_l2;
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  _loop_l2->v())) {
            auto _value = *_loop_l1;
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_value)))
                    : _root.emplace(std::move(_value)));
            break;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
            if (cmp(a0, a00)) {
              auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
              List<uint64_t> &_node =
                  (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                  std::move(_cell)))
                          : _root.emplace(std::move(_cell)));
              _write =
                  &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
              _loop_l2 = &*_loop_l2;
              _loop_l1 = crane_raw(a1);
              _loop_fuel = f;
              continue;
            } else {
              auto _cell = typename List<uint64_t>::Cons(a00, nullptr);
              List<uint64_t> &_node =
                  (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                  std::move(_cell)))
                          : _root.emplace(std::move(_cell)));
              _write =
                  &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
              _loop_l2 = crane_raw(a10);
              _loop_l1 = &*_loop_l1;
              _loop_fuel = f;
              continue;
            }
          }
        }
      }
    }
    return std::move(*_root);
  }

  template <typename F0>
  static List<uint64_t> merge_by(F0 &&cmp, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    return merge_by_fuel((len_impl<uint64_t>(l1) + len_impl<uint64_t>(l2)), cmp,
                         l1, l2);
  }

  /// remove_duplicates removes consecutive duplicates from sorted list.
  static List<uint64_t> remove_duplicates(const List<uint64_t> &l);
  /// uniq_sorted variant that preserves order.
  static List<uint64_t> uniq_sorted_aux(uint64_t prev, bool seen,
                                        const List<uint64_t> &l);
  static List<uint64_t> uniq_sorted(const List<uint64_t> &l);
};
