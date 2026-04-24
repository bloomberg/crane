#include <currying.h>

#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int Currying::add3(const unsigned int &a,
                                                  const unsigned int &b,
                                                  const unsigned int &c) {
  return (a + (b + c));
}

__attribute__((pure)) unsigned int
Currying::add3_partial1(const unsigned int &_x0, const unsigned int &_x1) {
  return add3(1u, _x0, _x1);
}

__attribute__((pure)) unsigned int
Currying::add3_partial2(const unsigned int &_x0) {
  return add3(1u, 2u, _x0);
}

__attribute__((pure)) unsigned int
Currying::pair_add(const Currying::pair<unsigned int, unsigned int> &p) {
  const auto &[d_a0, d_a1] =
      std::get<typename Currying::pair<unsigned int, unsigned int>::Pair0>(
          p.v());
  return (d_a0 + d_a1);
}

__attribute__((pure)) unsigned int
Currying::curried_add(const unsigned int &_x0, const unsigned int &_x1) {
  return curry<unsigned int, unsigned int, unsigned int>(pair_add, _x0, _x1);
}

__attribute__((pure)) unsigned int Currying::uncurried_add3(
    const Currying::pair<unsigned int,
                         Currying::pair<unsigned int, unsigned int>> &p) {
  const auto &[d_a0, d_a1] = std::get<typename Currying::pair<
      unsigned int, Currying::pair<unsigned int, unsigned int>>::Pair0>(p.v());
  auto &&_sv0 = clone_as_value<pair<unsigned int, unsigned int>>(d_a1);
  const auto &[d_a00, d_a10] =
      std::get<typename Currying::pair<unsigned int, unsigned int>::Pair0>(
          _sv0.v());
  return add3(d_a0, d_a00, d_a10);
}

__attribute__((pure)) unsigned int Currying::sub(const unsigned int &_x0,
                                                 const unsigned int &_x1) {
  return (((_x0 - _x1) > _x0 ? 0 : (_x0 - _x1)));
}

__attribute__((pure)) unsigned int
Currying::flipped_sub(const unsigned int &_x0, const unsigned int &_x1) {
  return flip<unsigned int, unsigned int, unsigned int>(sub, _x0, _x1);
}

__attribute__((pure)) unsigned int Currying::add_base(const unsigned int &_x0,
                                                      const unsigned int &_x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int Currying::add_ten(const unsigned int &_x0) {
  return add_base((2u * 5u), _x0);
}
