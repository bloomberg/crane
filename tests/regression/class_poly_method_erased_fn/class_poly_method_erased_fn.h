#ifndef INCLUDED_CLASS_POLY_METHOD_ERASED_FN
#define INCLUDED_CLASS_POLY_METHOD_ERASED_FN

#include "fn.h"
#include "obj.h"
#include <concepts>
#include <cstdint>
#include <utility>

/// A typeclass method polymorphic in its own type argument
/// (`forall A, (A -> A) -> A -> A`): the instance takes the erased
/// `std::function<std::any(std::any)>`, so the projection must adapt the
/// caller's concrete closure to it.

template <typename I>
concept Mapper = requires {
  {
    I::template mapf<crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<crane::obj>())
  } -> std::convertible_to<crane::obj>;
};

struct ClassPolyMethodErasedFn {
  template <Mapper _tcI0, typename T1, typename F0>
  static T1 mapf(F0 &&x, const T1 &x0) {
    return _tcI0::template mapf<T1>(x, x0);
  }

  struct Twice {
    template <typename CraneA0>
    static CraneA0 mapf(crane::fn<CraneA0(CraneA0)> f, CraneA0 x) {
      return f(f(std::move(x)));
    }
  };

  static_assert(Mapper<Twice>);
  static inline const uint64_t go = Twice::template mapf<uint64_t>(
      [](uint64_t n) { return (n + UINT64_C(3)); }, UINT64_C(1));
};

#endif // INCLUDED_CLASS_POLY_METHOD_ERASED_FN
