#include <algorithm>
#include <any>
#include <functional>
#include <implicit_args.h>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ImplicitArgs::add_one(const unsigned int _x0) {
  return [](const unsigned int _x0) { return (1u + _x0); }(_x0);
}

unsigned int ImplicitArgs::double_nat(const unsigned int n) { return (n + n); }

unsigned int ImplicitArgs::add_implicit(const unsigned int _x0,
                                        const unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int ImplicitArgs::scale(const unsigned int _x0,
                                 const unsigned int _x1) {
  return (_x0 * _x1);
}

unsigned int ImplicitArgs::combine(const unsigned int a, const unsigned int b,
                                   const unsigned int x) {
  return (a + (b + x));
}

unsigned int ImplicitArgs::with_base(const unsigned int _x0,
                                     const unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int ImplicitArgs::from_zero(const unsigned int _x0) {
  return [](const unsigned int _x0) { return with_base(0u, _x0); }(_x0);
}

unsigned int ImplicitArgs::from_ten(const unsigned int _x0) {
  return [](const unsigned int _x0) { return with_base(10u, _x0); }(_x0);
}

unsigned int ImplicitArgs::sum_with_init(
    const unsigned int init,
    const std::shared_ptr<ImplicitArgs::mylist<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [&](const typename ImplicitArgs::mylist<unsigned int>::mynil _args)
              -> unsigned int { return init; },
          [&](const typename ImplicitArgs::mylist<unsigned int>::mycons _args)
              -> unsigned int {
            unsigned int x = _args._a0;
            std::shared_ptr<ImplicitArgs::mylist<unsigned int>> rest =
                _args._a1;
            return (x + sum_with_init(init, rest));
          }},
      l->v());
}

unsigned int ImplicitArgs::nested_implicits(const unsigned int a,
                                            const unsigned int b,
                                            const unsigned int c) {
  return (a + (b + c));
}

unsigned int
ImplicitArgs::choose_branch(const std::shared_ptr<Bool0::bool0> &flag,
                            const unsigned int t, const unsigned int f) {
  return std::visit(
      Overloaded{[&](const typename Bool0::bool0::true0 _args) -> unsigned int {
                   return t;
                 },
                 [&](const typename Bool0::bool0::false0 _args)
                     -> unsigned int { return f; }},
      flag->v());
}
