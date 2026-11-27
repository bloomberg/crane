#include "poly_sum_payload_obj.h"

unsigned int Ascii0::N_of_digits(const List<bool> &l) {
  if (std::holds_alternative<typename List<bool>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename List<bool>::Cons>(l.v());
    return (a0 ? 1u : 0u) + 2u * Ascii0::N_of_digits(*a1);
  }
}

unsigned int Ascii0::N_of_ascii(const Ascii &a) {
  const auto &[a8, a9, a10, a11, a12, a13, a14, a15] = a;
  return Ascii0::N_of_digits(List<bool>::cons(
      a8,
      List<bool>::cons(
          a9,
          List<bool>::cons(
              a10,
              List<bool>::cons(
                  a11, List<bool>::cons(
                           a12, List<bool>::cons(
                                    a13, List<bool>::cons(
                                             a14, List<bool>::cons(
                                                      a15,
                                                      List<bool>::nil())))))))));
}

uint64_t Ascii0::nat_of_ascii(const Ascii &a) {
  return static_cast<uint64_t>(Ascii0::N_of_ascii(a));
}
