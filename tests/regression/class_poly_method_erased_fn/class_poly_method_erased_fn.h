#ifndef INCLUDED_CLASS_POLY_METHOD_ERASED_FN
#define INCLUDED_CLASS_POLY_METHOD_ERASED_FN

#include "crane_fn.h"
#include <any>
#include <concepts>
#include <functional>
#include <utility>

/// A typeclass method polymorphic in its own type argument
/// (`forall A, (A -> A) -> A -> A`): the instance takes the erased
/// `std::function<std::any(std::any)>`, so the projection must adapt the
/// caller's concrete closure to it.

template <typename I>
concept Mapper = requires {
  {
    I::mapf(std::declval<std::function<std::any(std::any)>>(),
            std::declval<std::any>())
  } -> std::convertible_to<std::any>;
};

struct ClassPolyMethodErasedFn {
  template <Mapper _tcI0, typename T1, typename F0>
  static T1 mapf(F0 &&x, const T1 &x0) {
    return std::any_cast<T1>(_tcI0::mapf(crane_erase_fn(x), x0));
  }

  struct Twice {
    static std::any mapf(std::function<std::any(std::any)> f, std::any x) {
      return f(f(x));
    }
  };

  static_assert(Mapper<Twice>);
  static inline const uint64_t go = mapf<Twice, uint64_t>(
      [](uint64_t n) { return (n + UINT64_C(3)); }, UINT64_C(1));
};

#endif // INCLUDED_CLASS_POLY_METHOD_ERASED_FN
