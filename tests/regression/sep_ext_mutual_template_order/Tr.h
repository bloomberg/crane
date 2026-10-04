#ifndef INCLUDED_TR
#define INCLUDED_TR

#include <type_traits>
#include <variant>

#include "Ty.h"

namespace Tr {

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
Ty::Tree<T2> tmap(F0 &&f, const Ty::Tree<T1> &t);
template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
Ty::Forest<T2> fmap(F0 &&f, const Ty::Forest<T1> &fs);

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
Ty::Tree<T2> tmap(F0 &&f, const Ty::Tree<T1> &t) {
  const auto &[a0, a1] = std::get<typename Ty::Tree<T1>::Node>(t.v());
  return Ty::template Tree<T2>::node(f(a0), fmap<T1, T2>(f, *a1));
}

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
Ty::Forest<T2> fmap(F0 &&f, const Ty::Forest<T1> &fs) {
  if (std::holds_alternative<typename Ty::Forest<T1>::Nil>(fs.v())) {
    return Ty::template Forest<T2>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename Ty::Forest<T1>::Cons>(fs.v());
    return Ty::template Forest<T2>::cons(tmap<T1, T2>(f, *a0),
                                         fmap<T1, T2>(f, *a1));
  }
}

} // namespace Tr

#endif // INCLUDED_TR
