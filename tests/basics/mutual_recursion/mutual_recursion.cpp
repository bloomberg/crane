#include <mutual_recursion.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool MutualRecursion::is_even(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int m = n - 1;
    return is_odd(m);
  }
}

__attribute__((pure)) bool MutualRecursion::is_odd(const unsigned int n) {
  if (n <= 0) {
    return false;
  } else {
    unsigned int m = n - 1;
    return is_even(m);
  }
}

__attribute__((pure)) unsigned int MutualRecursion::tree_sum(
    const std::shared_ptr<MutualRecursion::tree<unsigned int>> &t) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecursion::tree<unsigned int>::Leaf &_args)
              -> unsigned int { return _args.d_a0; },
          [](const typename MutualRecursion::tree<unsigned int>::Node &_args)
              -> unsigned int { return forest_sum(_args.d_a0); }},
      t->v());
}

__attribute__((pure)) unsigned int MutualRecursion::forest_sum(
    const std::shared_ptr<MutualRecursion::forest<unsigned int>> &f) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecursion::forest<unsigned int>::Empty &)
              -> unsigned int { return 0u; },
          [](const typename MutualRecursion::forest<unsigned int>::Trees &_args)
              -> unsigned int {
            return (tree_sum(_args.d_a0) + forest_sum(_args.d_a1));
          }},
      f->v());
}
