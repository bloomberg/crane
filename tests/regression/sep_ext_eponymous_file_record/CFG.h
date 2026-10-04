#ifndef INCLUDED_CFG
#define INCLUDED_CFG

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <stdexcept>
#include <utility>

#include "Datatypes.h"

namespace CFG {

template <typename T> struct cfg;

template <typename T> struct cfg {
  T init;
  typename Datatypes::template List<T> rest;

  // ACCESSORS
  template <typename _U> operator cfg<_U>() const {
    return {[&]() -> _U {
              if constexpr (crane_convertible<_U, const T &>) {
                return crane_convert<_U>(init);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            crane_convert<typename Datatypes::template List<_U>>(rest)};
  }
};

template <typename T1> T1 first(const cfg<T1> &c) { return c.init; }

template <typename T1> std::pair<T1, T1> first_twice(const cfg<T1> &c) {
  return std::make_pair(first<T1>(c), first<T1>(c));
}

} // namespace CFG

#endif // INCLUDED_CFG
