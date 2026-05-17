#include "implicit_args.h"

uint64_t ImplicitArgs::add_one(uint64_t _x0) { return (UINT64_C(1) + _x0); }

uint64_t ImplicitArgs::double_nat(uint64_t n) { return (n + n); }

uint64_t ImplicitArgs::add_implicit(uint64_t _x0, uint64_t _x1) {
  return (_x0 + _x1);
}

uint64_t ImplicitArgs::scale(uint64_t _x0, uint64_t _x1) { return (_x0 * _x1); }

uint64_t ImplicitArgs::combine(uint64_t a, uint64_t b, uint64_t x) {
  return (a + (b + x));
}

uint64_t ImplicitArgs::with_base(uint64_t _x0, uint64_t _x1) {
  return (_x0 + _x1);
}

uint64_t ImplicitArgs::from_zero(uint64_t _x0) {
  return with_base(UINT64_C(0), _x0);
}

uint64_t ImplicitArgs::from_ten(uint64_t _x0) {
  return with_base(UINT64_C(10), _x0);
}

uint64_t ImplicitArgs::sum_with_init(uint64_t init,
                                     const ImplicitArgs::mylist<uint64_t> &l) {
  if (std::holds_alternative<typename ImplicitArgs::mylist<uint64_t>::Mynil>(
          l.v())) {
    return init;
  } else {
    const auto &[a0, a1] =
        std::get<typename ImplicitArgs::mylist<uint64_t>::Mycons>(l.v());
    return (a0 + sum_with_init(init, *a1));
  }
}

uint64_t ImplicitArgs::nested_implicits(uint64_t a, uint64_t b, uint64_t c) {
  return (a + (b + c));
}

uint64_t ImplicitArgs::choose_branch(bool flag, uint64_t t, uint64_t f) {
  if (flag) {
    return t;
  } else {
    return f;
  }
}
