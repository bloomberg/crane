#include "mutual_mod.h"

uint64_t EvenOdd::even_length(const EvenOdd::even_list &e) {
  if (std::holds_alternative<typename EvenOdd::even_list::ENil>(e.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename EvenOdd::even_list::ECons>(e.v());
    return (odd_length(*a1) + 1);
  }
}

uint64_t EvenOdd::odd_length(const EvenOdd::odd_list &o) {
  const auto &[a0, a1] = std::get<typename EvenOdd::odd_list::OCons>(o.v());
  return (even_length(*a1) + 1);
}
