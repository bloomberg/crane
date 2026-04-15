#include <implicit_args.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ImplicitArgs::add_one(const unsigned int _x0) {
  return (1u + _x0);
}

__attribute__((pure)) unsigned int
ImplicitArgs::double_nat(const unsigned int n) {
  return (n + n);
}

__attribute__((pure)) unsigned int
ImplicitArgs::add_implicit(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int ImplicitArgs::scale(const unsigned int _x0,
                                                       const unsigned int _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) unsigned int ImplicitArgs::combine(const unsigned int a,
                                                         const unsigned int b,
                                                         const unsigned int x) {
  return (a + (b + x));
}

__attribute__((pure)) unsigned int
ImplicitArgs::with_base(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int
ImplicitArgs::from_zero(const unsigned int _x0) {
  return with_base(0u, _x0);
}

__attribute__((pure)) unsigned int
ImplicitArgs::from_ten(const unsigned int _x0) {
  return with_base(10u, _x0);
}

__attribute__((pure)) unsigned int ImplicitArgs::sum_with_init(
    const unsigned int init,
    const std::shared_ptr<ImplicitArgs::mylist<unsigned int>> &l) {
  if (std::holds_alternative<
          typename ImplicitArgs::mylist<unsigned int>::Mynil>(l->v())) {
    return init;
  } else {
    const auto &_m =
        *std::get_if<typename ImplicitArgs::mylist<unsigned int>::Mycons>(
            &l->v());
    return (_m.d_a0 + sum_with_init(init, _m.d_a1));
  }
}

__attribute__((pure)) unsigned int
ImplicitArgs::nested_implicits(const unsigned int a, const unsigned int b,
                               const unsigned int c) {
  return (a + (b + c));
}

__attribute__((pure)) unsigned int
ImplicitArgs::choose_branch(const bool flag, const unsigned int t,
                            const unsigned int f) {
  if (flag) {
    return t;
  } else {
    return f;
  }
}
