#ifndef INCLUDED_LOOPIFY_NESTED_CALL_FRAME_FIELD
#define INCLUDED_LOOPIFY_NESTED_CALL_FRAME_FIELD

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

template <typename A>
struct List; /// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential

/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Under Loopify, g r (g r a) in two places of the same branch (one under a
/// pair match, one inside a filter predicate): the second continuation frame
/// is built as _after_g_in_pair_2{a, a1} with the const List & where its
/// field is a std::shared_ptr: "no viable conversion from 'const List<...>'
/// to 'std::shared_ptr<List<...>>'".
struct LoopifyNestedCallFrameField {
  static List<uint64_t> g(const List<std::pair<uint64_t, bool>> &l,
                          const List<uint64_t> &a);
};

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

  template <typename F0> List<A> filter(F0 &&f) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<A>::nil();
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          auto _cell = typename List<A>::Cons(a0, nullptr);
          List<A> &_node =
              (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        } else {
          _loop_self = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

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
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_NESTED_CALL_FRAME_FIELD
