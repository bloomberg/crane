#ifndef INCLUDED_TT_AT_COMPUTED_TYPE
#define INCLUDED_TT_AT_COMPUTED_TYPE

#include "crane_fn.h"
#include "obj.h"
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
};

/// tt returned where the result type is computed by a type-level function.
///
/// tuple (nats n) is unit at 0 and a pair otherwise; erased, it
/// is the box, which holds tt as well as it holds a pair.  The 0 branch
/// of ones is reachable -- every call ends there -- so it must return its
/// tt, not be taken for a branch a dependent match rules out.
struct TtAtComputedType {
  using tuple = crane::obj;
  static List<crane::obj> nats(uint64_t n);
  static tuple ones(uint64_t n);
  static inline const uint64_t first =
      crane_any_cast<std::pair<uint64_t, std::monostate>>(ones(UINT64_C(1)))
          .first;

  static inline const uint64_t second =
      crane_any_cast<std::pair<uint64_t, std::monostate>>(
          crane_any_cast<
              std::pair<uint64_t, std::pair<uint64_t, std::monostate>>>(
              ones(UINT64_C(2)))
              .second)
          .first;
};

#endif // INCLUDED_TT_AT_COMPUTED_TYPE
