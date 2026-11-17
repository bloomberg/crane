#ifndef INCLUDED_LOOPIFY_ADVANCED_LISTS
#define INCLUDED_LOOPIFY_ADVANCED_LISTS

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

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
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

struct LoopifyAdvancedLists {
  static uint64_t product(const List<uint64_t> &l);
  static List<uint64_t> compress(const List<uint64_t> &l);
  static List<uint64_t> pairwise_sum(const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  group_pairs(const List<uint64_t> &l);
  static List<uint64_t> interleave(const List<uint64_t> &l1,
                                   const List<uint64_t> &l2);
  static List<uint64_t> concat_lists(const List<List<uint64_t>> &ll);

  template <typename F0>
    requires std::is_invocable_r_v<List<uint64_t>, F0 &, uint64_t &>
  static List<uint64_t> flat_map(F0 &&f, const List<uint64_t> &l) {
    // Explicit stack replaces the non-tail recursion of flat_map: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<uint64_t> *l;
    };

    struct _after_flat_map_in_Cons {
      uint64_t a0;
    };

    using _frame = std::variant<_call, _after_flat_map_in_Cons>;
    List<uint64_t> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame _popped = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_after_flat_map_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_flat_map_in_Cons>(_popped));
        uint64_t a0 = _f.a0;
        _result = f(a0).app(std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool all_satisfy(F0 &&p, const List<uint64_t> &l) {
    // Explicit stack replaces the non-tail recursion of all_satisfy: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const List<uint64_t> *l;
    };

    struct _after_all_satisfy_in_Cons {
      uint64_t a0;
    };

    using _frame = std::variant<_call, _after_all_satisfy_in_Cons>;
    bool _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame _popped = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_after_all_satisfy_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_all_satisfy_in_Cons>(_popped));
        uint64_t a0 = _f.a0;
        _result = (p(a0) && std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool any_satisfy(F0 &&p, const List<uint64_t> &l) {
    // Explicit stack replaces the non-tail recursion of any_satisfy: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const List<uint64_t> *l;
    };

    struct _after_any_satisfy_in_Cons {
      uint64_t a0;
    };

    using _frame = std::variant<_call, _after_any_satisfy_in_Cons>;
    bool _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame _popped = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = false;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_after_any_satisfy_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_any_satisfy_in_Cons>(_popped));
        uint64_t a0 = _f.a0;
        _result = (p(a0) || std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
  static std::optional<uint64_t> find_first(F0 &&p, const List<uint64_t> &l) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<uint64_t>(a0);
        } else {
          _loop_l = crane_raw(a1);
        }
      }
    }
  }
};

#endif // INCLUDED_LOOPIFY_ADVANCED_LISTS
