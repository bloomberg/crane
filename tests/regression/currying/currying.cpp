#include <algorithm>
#include <any>
#include <currying.h>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

unsigned int Currying::add3(const unsigned int a, const unsigned int b,
                            const unsigned int c) {
  return (a + (b + c));
}

unsigned int Currying::add3_partial1(const unsigned int _x0,
                                     const unsigned int _x1) {
  return [](const unsigned int _x0, const unsigned int _x1) {
    return add3(1u, _x0, _x1);
  }(_x0, _x1);
}

unsigned int Currying::add3_partial2(const unsigned int _x0) {
  return [](const unsigned int _x0) { return add3(1u, 2u, _x0); }(_x0);
}

unsigned int Currying::pair_add(
    const std::shared_ptr<Currying::pair<unsigned int, unsigned int>> &p) {
  return std::visit(
      Overloaded{
          [](const typename Currying::pair<unsigned int, unsigned int>::Pair
                 _args) -> unsigned int {
            unsigned int a = _args._a0;
            unsigned int b = _args._a1;
            return (a + b);
          }},
      p->v());
}

unsigned int Currying::curried_add(const unsigned int _x0,
                                   const unsigned int _x1) {
  return [](const unsigned int _x0, const unsigned int _x1) {
    return curry<unsigned int, unsigned int, unsigned int>(pair_add, _x0, _x1);
  }(_x0, _x1);
}

unsigned int Currying::uncurried_add3(
    const std::shared_ptr<Currying::pair<
        unsigned int,
        std::shared_ptr<Currying::pair<unsigned int, unsigned int>>>> &p) {
  return std::visit(
      Overloaded{
          [](const typename Currying::pair<
              unsigned int,
              std::shared_ptr<Currying::pair<unsigned int, unsigned int>>>::Pair
                 _args) -> unsigned int {
            unsigned int a = _args._a0;
            std::shared_ptr<Currying::pair<unsigned int, unsigned int>> bc =
                _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename Currying::pair<unsigned int,
                                                      unsigned int>::Pair _args)
                        -> unsigned int {
                      unsigned int b = _args._a0;
                      unsigned int c = _args._a1;
                      return add3(a, b, c);
                    }},
                bc->v());
          }},
      p->v());
}

unsigned int Currying::sub(const unsigned int _x0, const unsigned int _x1) {
  return (((_x0 - _x1) > _x0 ? 0 : (_x0 - _x1)));
}

unsigned int Currying::flipped_sub(const unsigned int _x0,
                                   const unsigned int _x1) {
  return [](const unsigned int _x0, const unsigned int _x1) {
    return flip<unsigned int, unsigned int, unsigned int>(sub, _x0, _x1);
  }(_x0, _x1);
}

unsigned int Currying::add_base(const unsigned int _x0,
                                const unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int Currying::add_ten(const unsigned int _x0) {
  return [](const unsigned int _x0) { return add_base((2u * 5u), _x0); }(_x0);
}
