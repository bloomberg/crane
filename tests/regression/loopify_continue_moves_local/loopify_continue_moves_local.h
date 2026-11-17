#ifndef INCLUDED_LOOPIFY_CONTINUE_MOVES_LOCAL
#define INCLUDED_LOOPIFY_CONTINUE_MOVES_LOCAL

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
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

  List<A> tl() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[_, a1] = std::get<typename List<A>::Cons>(this->v());
      return *a1;
    }
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

/// A tail loop moves a local of its turn into a parameter's next value
/// where the turn owns it and reads it there for the last time
/// (Ownership_ir.continue_moves, Move_argument): where nothing reads it
/// after but the Continue's other arguments, by name, it is moved at the
/// last of the loop's updates that reads it.  A part of it read by another
/// argument keeps it copied.
struct LoopifyContinueMovesLocal {
  static List<uint64_t> count_down(uint64_t n, List<uint64_t> acc);
  /// next is read by the count as well, which is updated first.
  static std::pair<List<uint64_t>, uint64_t>
  count_both(uint64_t n, const List<uint64_t> &acc, uint64_t k);
  /// The local is passed to one parameter, its tail, computed by a call
  /// on it, to another.
  static std::pair<List<uint64_t>, List<uint64_t>>
  split_off(uint64_t n, const List<uint64_t> &acc, const List<uint64_t> &rest);
  /// The local is passed to one parameter, the tail its match binds to
  /// another: a part of it, read by name only there, so it is copied.
  static std::pair<List<uint64_t>, List<uint64_t>>
  peel(uint64_t n, const List<uint64_t> &acc, const List<uint64_t> &rest);
  static inline const List<uint64_t> test_count_down =
      count_down(UINT64_C(3), List<uint64_t>::nil());
  static inline const std::pair<List<uint64_t>, uint64_t> test_count_both =
      count_both(UINT64_C(3), List<uint64_t>::nil(), UINT64_C(0));
  static inline const std::pair<List<uint64_t>, List<uint64_t>> test_split_off =
      split_off(UINT64_C(3), List<uint64_t>::nil(), List<uint64_t>::nil());
  static inline const std::pair<List<uint64_t>, List<uint64_t>> test_peel =
      peel(UINT64_C(3), List<uint64_t>::nil(), List<uint64_t>::nil());
};

#endif // INCLUDED_LOOPIFY_CONTINUE_MOVES_LOCAL
