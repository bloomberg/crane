#include "implicit_args.h"

unsigned int ImplicitArgs::add_one(unsigned int _x0) { return (1u + _x0); }

unsigned int ImplicitArgs::double_nat(unsigned int n) { return (n + n); }

unsigned int ImplicitArgs::add_implicit(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int ImplicitArgs::scale(unsigned int _x0, unsigned int _x1) {
  return (_x0 * _x1);
}

unsigned int ImplicitArgs::combine(unsigned int a, unsigned int b,
                                   unsigned int x) {
  return (a + (b + x));
}

unsigned int ImplicitArgs::with_base(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int ImplicitArgs::from_zero(unsigned int _x0) {
  return with_base(0u, _x0);
}

unsigned int ImplicitArgs::from_ten(unsigned int _x0) {
  return with_base(10u, _x0);
}

unsigned int
ImplicitArgs::sum_with_init(unsigned int init,
                            const ImplicitArgs::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename ImplicitArgs::mylist<unsigned int>::Mynil>(l.v())) {
    return init;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ImplicitArgs::mylist<unsigned int>::Mycons>(l.v());
    return (d_a0 + sum_with_init(init, *d_a1));
  }
}

unsigned int ImplicitArgs::nested_implicits(unsigned int a, unsigned int b,
                                            unsigned int c) {
  return (a + (b + c));
}

unsigned int ImplicitArgs::choose_branch(bool flag, unsigned int t,
                                         unsigned int f) {
  if (flag) {
    return t;
  } else {
    return f;
  }
}
