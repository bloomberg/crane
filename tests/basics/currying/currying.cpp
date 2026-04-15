#include <currying.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int Currying::add3(const unsigned int a,
                                                  const unsigned int b,
                                                  const unsigned int c) {
  return (a + (b + c));
}

__attribute__((pure)) unsigned int
Currying::add3_partial1(const unsigned int _x0, const unsigned int _x1) {
  return add3(1u, _x0, _x1);
}

__attribute__((pure)) unsigned int
Currying::add3_partial2(const unsigned int _x0) {
  return add3(1u, 2u, _x0);
}

__attribute__((pure)) unsigned int Currying::pair_add(
    const std::shared_ptr<Currying::pair<unsigned int, unsigned int>> &p) {
  const auto &_m =
      *std::get_if<typename Currying::pair<unsigned int, unsigned int>::Pair0>(
          &p->v());
  return (_m.d_a0 + _m.d_a1);
}

__attribute__((pure)) unsigned int
Currying::curried_add(const unsigned int _x0, const unsigned int _x1) {
  return curry<unsigned int, unsigned int, unsigned int>(pair_add, _x0, _x1);
}

__attribute__((pure)) unsigned int Currying::uncurried_add3(
    const std::shared_ptr<Currying::pair<
        unsigned int,
        std::shared_ptr<Currying::pair<unsigned int, unsigned int>>>> &p) {
  const auto &_m = *std::get_if<typename Currying::pair<
      unsigned int,
      std::shared_ptr<Currying::pair<unsigned int, unsigned int>>>::Pair0>(
      &p->v());
  auto &&_sv0 = _m.d_a1;
  const auto &_m0 =
      *std::get_if<typename Currying::pair<unsigned int, unsigned int>::Pair0>(
          &_sv0->v());
  return add3(_m.d_a0, _m0.d_a0, _m0.d_a1);
}

__attribute__((pure)) unsigned int Currying::sub(const unsigned int _x0,
                                                 const unsigned int _x1) {
  return (((_x0 - _x1) > _x0 ? 0 : (_x0 - _x1)));
}

__attribute__((pure)) unsigned int
Currying::flipped_sub(const unsigned int _x0, const unsigned int _x1) {
  return flip<unsigned int, unsigned int, unsigned int>(sub, _x0, _x1);
}

__attribute__((pure)) unsigned int Currying::add_base(const unsigned int _x0,
                                                      const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int Currying::add_ten(const unsigned int _x0) {
  return add_base((2u * 5u), _x0);
}
