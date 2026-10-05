#ifndef INCLUDED_CFG
#define INCLUDED_CFG

#include "crane_fn.h"
#include "obj.h"
#include <stdexcept>
#include <utility>

#include "Datatypes.h"

namespace CFG {

template <typename T> struct cfg;

template <typename T> struct cfg {
  T init;
  typename Datatypes::template List<T> rest;

  // ACCESSORS
  template <typename CraneU> operator cfg<CraneU>() const {
    return {[&]() -> CraneU {
              if constexpr (crane_convertible<CraneU, const T &>) {
                return crane_convert<CraneU>(init);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            crane_convert<typename Datatypes::template List<CraneU>>(rest)};
  }
};

template <typename T1> T1 first(const cfg<T1> &c) { return c.init; }

template <typename T1> std::pair<T1, T1> first_twice(const cfg<T1> &c) {
  return std::make_pair(first<T1>(c), first<T1>(c));
}

} // namespace CFG

#endif // INCLUDED_CFG
