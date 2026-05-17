#ifndef INCLUDED_SEPEXTNULLARYCALL
#define INCLUDED_SEPEXTNULLARYCALL

#include <concepts>

#include "Datatypes.h"
#include "List.h"

namespace SepExtNullaryCall {

template <typename M>
concept Cfg = requires {
  requires(
      requires {
        { M::default_val } -> std::convertible_to<unsigned int>;
      } ||
      requires {
        { M::default_val() } -> std::convertible_to<unsigned int>;
      });
  requires(
      requires {
        {
          M::default_list
        } -> std::convertible_to<Datatypes::List<unsigned int>>;
      } ||
      requires {
        {
          M::default_list()
        } -> std::convertible_to<Datatypes::List<unsigned int>>;
      });
};

template <Cfg C> struct Worker {
  static const unsigned int &get_default() {
    static const unsigned int v = C::default_val();
    return v;
  }

  static const typename Datatypes::template List<unsigned int> &local_empty() {
    static const typename Datatypes::template List<unsigned int> v =
        Datatypes::template List<unsigned int>::nil();
    return v;
  }

  static const unsigned int &local_length() {
    static const unsigned int v = local_empty().length();
    return v;
  }

  static typename Datatypes::template List<unsigned int>
  prepend(unsigned int x) {
    return Datatypes::template List<unsigned int>::cons(x, C::default_list());
  }

  static const unsigned int &default_head() {
    static const unsigned int v = C::default_list().hd(0u);
    return v;
  }
};

} // namespace SepExtNullaryCall

#endif // INCLUDED_SEPEXTNULLARYCALL
