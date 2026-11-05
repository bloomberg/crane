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

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
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
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return *a1;
    }
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

/// A tail loop moves a local of its turn into a parameter's next value
/// where the turn owns it and reads it there for the last time
/// (Ownership_plan.continue_moves, Move_argument): where nothing reads it
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
