#include "mutual_recursion.h"

bool MutualRecursion::is_even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t m = n - 1;
    return is_odd(m);
  }
}

bool MutualRecursion::is_odd(uint64_t n) {
  if (n <= 0) {
    return false;
  } else {
    uint64_t m = n - 1;
    return is_even(m);
  }
}

uint64_t MutualRecursion::tree_sum(const MutualRecursion::tree<uint64_t> &t) {
  if (std::holds_alternative<typename MutualRecursion::tree<uint64_t>::Leaf>(
          t.v())) {
    const auto &[a0] =
        std::get<typename MutualRecursion::tree<uint64_t>::Leaf>(t.v());
    return a0;
  } else {
    const auto &[a0] =
        std::get<typename MutualRecursion::tree<uint64_t>::Node>(t.v());
    return forest_sum(*a0);
  }
}

uint64_t
MutualRecursion::forest_sum(const MutualRecursion::forest<uint64_t> &f) {
  if (std::holds_alternative<typename MutualRecursion::forest<uint64_t>::Empty>(
          f.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename MutualRecursion::forest<uint64_t>::Trees>(f.v());
    return (tree_sum(*a0) + forest_sum(*a1));
  }
}
