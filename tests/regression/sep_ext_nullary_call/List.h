#ifndef INCLUDED_LIST
#define INCLUDED_LIST

#include <variant>

#include "Datatypes.h"

namespace List {

template <typename T1> T1 hd(T1 default0, const Datatypes::List<T1> &l) {
  if (std::holds_alternative<typename Datatypes::List<T1>::Nil>(l.v())) {
    return default0;
  } else {
    const auto &[a0, a1] = std::get<typename Datatypes::List<T1>::Cons>(l.v());
    return a0;
  }
}

} // namespace List

#endif // INCLUDED_LIST
