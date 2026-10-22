#ifndef INCLUDED_LOOPIFY_CAPTURE_MOVE_RENAMED
#define INCLUDED_LOOPIFY_CAPTURE_MOVE_RENAMED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {
  static bool even(uint64_t n);
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

/// A continuation captured by move, in a function loopified.
///
/// partition_cps hands the recursive call a new continuation that closes
/// over the old one, k, for the last time: the closure takes k by move.
/// Loopified, k becomes the loop variable _loop_k, and the closure is
/// written over it at every turn.  The closure's reads were renamed but its
/// capture move was not, so it went on moving from k, which the loop had
/// already moved into _loop_k on entry: a read of a moved-from value, and
/// the continuation it did read copied.
struct LoopifyCaptureMoveRenamed {
  static uint64_t
  partition_cps(crane::fn<bool(uint64_t)> p, const List<uint64_t> &l,
                crane::fn<uint64_t(List<uint64_t>, List<uint64_t>)> k) {
    crane::fn<uint64_t(List<uint64_t>, List<uint64_t>)> _loop_k = std::move(k);
    List<uint64_t> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        return _loop_k(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        const List<uint64_t> &a1_value = *a1;
        _loop_k = [=, _loop_k = std::move(_loop_k)](
                      const List<uint64_t> &yes,
                      const List<uint64_t> &no) -> uint64_t {
          if (p(a0)) {
            return _loop_k(List<uint64_t>::cons(a0, yes), no);
          } else {
            return _loop_k(yes, List<uint64_t>::cons(a0, no));
          }
        };
        _loop_l = a1_value;
      }
    }
  }

  static uint64_t count_evens(const List<uint64_t> &l);
  static uint64_t count_odds(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_CAPTURE_MOVE_RENAMED
