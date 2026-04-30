#include <implicit_args.h>

unsigned int ImplicitArgs::add_one(const unsigned int &_x0) {
  return (1u + _x0);
}

unsigned int ImplicitArgs::double_nat(const unsigned int &n) { return (n + n); }

unsigned int ImplicitArgs::add_implicit(const unsigned int &_x0,
                                        const unsigned int &_x1) {
  return (_x0 + _x1);
}

unsigned int ImplicitArgs::scale(const unsigned int &_x0,
                                 const unsigned int &_x1) {
  return (_x0 * _x1);
}

unsigned int ImplicitArgs::combine(const unsigned int &a, const unsigned int &b,
                                   const unsigned int &x) {
  return (a + (b + x));
}

unsigned int ImplicitArgs::with_base(const unsigned int &_x0,
                                     const unsigned int &_x1) {
  return (_x0 + _x1);
}

unsigned int ImplicitArgs::from_zero(const unsigned int &_x0) {
  return with_base(0u, _x0);
}

unsigned int ImplicitArgs::from_ten(const unsigned int &_x0) {
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
    return (d_a0 + sum_with_init(init, *(d_a1)));
  }
}

unsigned int ImplicitArgs::nested_implicits(const unsigned int &a,
                                            const unsigned int &b,
                                            const unsigned int &c) {
  return (a + (b + c));
}

unsigned int ImplicitArgs::choose_branch(const bool &flag, unsigned int t,
                                         unsigned int f) {
  if (flag) {
    return t;
  } else {
    return f;
  }
}
