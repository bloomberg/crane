#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <mutual_recursion.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

bool MutualRecursion::is_even(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int m = n - 1;
    return is_odd(m);
  }
}
bool MutualRecursion::is_odd(const unsigned int n) {
  if (n <= 0) {
    return false;
  } else {
    unsigned int m = n - 1;
    return is_even(m);
  }
}

unsigned int MutualRecursion::tree_sum(
    const std::shared_ptr<MutualRecursion::tree<unsigned int>> &t) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecursion::tree<unsigned int>::Leaf _args)
              -> unsigned int {
            unsigned int n = _args._a0;
            return std::move(n);
          },
          [](const typename MutualRecursion::tree<unsigned int>::Node _args)
              -> unsigned int {
            std::shared_ptr<MutualRecursion::forest<unsigned int>> f =
                _args._a0;
            return forest_sum(std::move(f));
          }},
      t->v());
}
unsigned int MutualRecursion::forest_sum(
    const std::shared_ptr<MutualRecursion::forest<unsigned int>> &f) {
  return std::visit(
      Overloaded{
          [](const typename MutualRecursion::forest<unsigned int>::Empty _args)
              -> unsigned int { return 0u; },
          [](const typename MutualRecursion::forest<unsigned int>::Trees _args)
              -> unsigned int {
            std::shared_ptr<MutualRecursion::tree<unsigned int>> t = _args._a0;
            std::shared_ptr<MutualRecursion::forest<unsigned int>> rest =
                _args._a1;
            return (tree_sum(std::move(t)) + forest_sum(std::move(rest)));
          }},
      f->v());
}
