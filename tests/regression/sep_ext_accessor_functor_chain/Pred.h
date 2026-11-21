#pragma once

#include <cstdint>

#include "Datatypes.h"

namespace Pred {
template <typename M>
concept T = requires {
  typename M::t;
};

template <T D> struct PredFn {
  using cache = typename Datatypes::template List<
      typename Datatypes::template List<typename D::t>>;

  static const cache &empty_cache() {
    static const cache v = Datatypes::template List<
        typename Datatypes::template List<typename D::t>>::nil();
    return v;
  }

  static uint64_t size(const cache &x0_) { return x0_.length(); }
};
} // namespace Pred
