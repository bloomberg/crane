#include <sigma_types.h>

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<SigT<unsigned int, std::any>>
SigmaTypes::nat_with_double(const unsigned int n) {
  return SigT<unsigned int, std::any>::existt((n + n), std::any{});
}

std::shared_ptr<Sig<unsigned int>>
SigmaTypes::positive_succ(const unsigned int n) {
  return Sig<unsigned int>::exist((n + 1));
}

__attribute__((pure)) unsigned int
SigmaTypes::get_positive(const unsigned int n) {
  return std::visit(
      Overloaded{[](const typename Sig<unsigned int>::Exist &_args) -> auto {
        return _args.d_x;
      }},
      positive_succ(n)->v());
}

std::shared_ptr<Sig<unsigned int>>
SigmaTypes::double_positive(const unsigned int n) {
  std::shared_ptr<Sig<unsigned int>> p = positive_succ(n);
  return Sig<unsigned int>::exist(
      (std::visit(Overloaded{[](const typename Sig<unsigned int>::Exist &_args)
                                 -> auto { return _args.d_x; }},
                  p->v()) +
       std::visit(Overloaded{[](const typename Sig<unsigned int>::Exist &_args0)
                                 -> auto { return _args0.d_x; }},
                  p->v())));
}

__attribute__((pure)) unsigned int
SigmaTypes::use_nat_double(const unsigned int n) {
  return nat_with_double(n)->projT1();
}

std::shared_ptr<List<unsigned int>>
SigmaTypes::positives_up_to(const unsigned int k) {
  if (k <= 0) {
    return List<unsigned int>::nil();
  } else {
    unsigned int k_ = k - 1;
    return List<unsigned int>::cons(
        std::visit(Overloaded{[](const typename Sig<unsigned int>::Exist &_args)
                                  -> auto { return _args.d_x; }},
                   positive_succ(k_)->v()),
        positives_up_to(k_));
  }
}
