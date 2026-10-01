#ifndef INCLUDED_FIX_ESCAPE_MATCH
#define INCLUDED_FIX_ESCAPE_MATCH

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct FixEscapeMatch {
  /// A local fixpoint inside a match branch capturing a pattern variable.
  /// The pattern variable h is a structured binding reference into the
  /// shared_ptr's data. The fixpoint captures it by &, then escapes
  /// through an option constructor. After the match IIFE returns,
  /// h is destroyed — invoking the closure is use-after-free.
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  make_fn_from_head(const List<uint64_t> &l);
  static inline const uint64_t test_match = []() -> uint64_t {
    auto _cs = make_fn_from_head(
        List<uint64_t>::cons(UINT64_C(10), List<uint64_t>::nil()));
    if (_cs.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(3));
    } else {
      return UINT64_C(0);
    }
  }();
  /// Variant: fixpoint captures TWO pattern variables from the match.
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  make_fn_from_pair(const List<uint64_t> &l);

  static inline const uint64_t test_match2 = []() -> uint64_t {
    auto _cs = make_fn_from_pair(List<uint64_t>::cons(
        UINT64_C(10),
        List<uint64_t>::cons(UINT64_C(20), List<uint64_t>::nil())));
    if (_cs.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(3));
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_FIX_ESCAPE_MATCH
