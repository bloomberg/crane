#include <mutual_recursion.h>

bool MutualRecursion::is_even(const unsigned int &n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int m = n - 1;
    return is_odd(m);
  }
}

bool MutualRecursion::is_odd(const unsigned int &n) {
  if (n <= 0) {
    return false;
  } else {
    unsigned int m = n - 1;
    return is_even(m);
  }
}

unsigned int
MutualRecursion::tree_sum(const MutualRecursion::tree<unsigned int> &t) {
  if (std::holds_alternative<
          typename MutualRecursion::tree<unsigned int>::Leaf>(t.v())) {
    const auto &[d_a0] =
        std::get<typename MutualRecursion::tree<unsigned int>::Leaf>(t.v());
    return d_a0;
  } else {
    const auto &[d_a0] =
        std::get<typename MutualRecursion::tree<unsigned int>::Node>(t.v());
    return forest_sum(*(d_a0));
  }
}

unsigned int
MutualRecursion::forest_sum(const MutualRecursion::forest<unsigned int> &f) {
  if (std::holds_alternative<
          typename MutualRecursion::forest<unsigned int>::Empty>(f.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MutualRecursion::forest<unsigned int>::Trees>(f.v());
    return (tree_sum(*(d_a0)) + forest_sum(*(d_a1)));
  }
}
