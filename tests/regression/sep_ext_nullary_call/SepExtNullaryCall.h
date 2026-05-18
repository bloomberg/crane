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
        { M::default_val } -> std::convertible_to<uint64_t>;
      } ||
      requires {
        { M::default_val() } -> std::convertible_to<uint64_t>;
      });
  requires(
      requires {
        { M::default_list } -> std::convertible_to<Datatypes::List<uint64_t>>;
      } ||
      requires {
        { M::default_list() } -> std::convertible_to<Datatypes::List<uint64_t>>;
      });
};

template <Cfg C> struct Worker {
  static const uint64_t &get_default() {
    static const uint64_t v = C::default_val();
    return v;
  }

  static const typename Datatypes::template List<uint64_t> &local_empty() {
    static const typename Datatypes::template List<uint64_t> v =
        Datatypes::template List<uint64_t>::nil();
    return v;
  }

  static const uint64_t &local_length() {
    static const uint64_t v = local_empty().length();
    return v;
  }

  static typename Datatypes::template List<uint64_t> prepend(uint64_t x) {
    return Datatypes::template List<uint64_t>::cons(x, C::default_list());
  }

  static const uint64_t &default_head() {
    static const uint64_t v = C::default_list().hd(UINT64_C(0));
    return v;
  }
};

} // namespace SepExtNullaryCall

#endif // INCLUDED_SEPEXTNULLARYCALL
