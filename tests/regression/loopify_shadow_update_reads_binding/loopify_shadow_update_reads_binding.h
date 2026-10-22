#ifndef INCLUDED_LOOPIFY_SHADOW_UPDATE_READS_BINDING
#define INCLUDED_LOOPIFY_SHADOW_UPDATE_READS_BINDING

#include "crane_fn.h"
#include "fn.h"
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

/// A tail loop whose new arguments read a field of the list it walks.
///
/// One call passes a fresh list, so fs is kept by value in _loop_fs,
/// and the match binds f and rest by reference into that value.  The
/// updates were staged in a temporary only where one names another's
/// variable, and f v names f, not _loop_fs: _loop_fs was assigned
/// rest first, and f then read the same storage, now the next cell's
/// function.
struct LoopifyShadowUpdateReadsBinding {
  static uint64_t apply_n(uint64_t n, uint64_t v,
                          const List<crane::fn<uint64_t(uint64_t)>> &fs);

  static inline const uint64_t result =
      apply_n(UINT64_C(4), UINT64_C(2),
              List<crane::fn<uint64_t(uint64_t)>>::cons(
                  [](uint64_t x) { return (x + UINT64_C(1)); },
                  List<crane::fn<uint64_t(uint64_t)>>::cons(
                      [](uint64_t x) { return (x * UINT64_C(10)); },
                      List<crane::fn<uint64_t(uint64_t)>>::cons(
                          [](uint64_t x) { return (x + UINT64_C(3)); },
                          List<crane::fn<uint64_t(uint64_t)>>::nil()))));
};

#endif // INCLUDED_LOOPIFY_SHADOW_UPDATE_READS_BINDING
