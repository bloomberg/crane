#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <sigma_types.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<SigT<unsigned int, std::any>>
SigmaTypes::nat_with_double(const unsigned int n) {
  return SigT<unsigned int, std::any>::ctor::existT_((n + n), std::any{});
}

std::shared_ptr<Sig<unsigned int>>
SigmaTypes::positive_succ(const unsigned int n) {
  return Sig<unsigned int>::ctor::exist_((std::move(n) + 1));
}

unsigned int SigmaTypes::get_positive(const unsigned int n) {
  return std::visit(
      Overloaded{[](const typename Sig<unsigned int>::exist _args) -> auto {
        auto a = _args._a0;
        return a;
      }},
      positive_succ(n)->v());
}

std::shared_ptr<Sig<unsigned int>>
SigmaTypes::double_positive(const unsigned int n) {
  std::shared_ptr<Sig<unsigned int>> p = positive_succ(n);
  return Sig<unsigned int>::ctor::exist_((
      std::visit(
          Overloaded{[](const typename Sig<unsigned int>::exist _args) -> auto {
            auto a = _args._a0;
            return a;
          }},
          p->v()) +
      std::visit(
          Overloaded{[](const typename Sig<unsigned int>::exist _args) -> auto {
            auto a = _args._a0;
            return a;
          }},
          p->v())));
}

unsigned int SigmaTypes::use_nat_double(const unsigned int n) {
  return nat_with_double(n)->projT1();
}

std::shared_ptr<List<unsigned int>>
SigmaTypes::positives_up_to(const unsigned int k) {
  if (k <= 0) {
    return List<unsigned int>::ctor::nil_();
  } else {
    unsigned int k_ = k - 1;
    return List<unsigned int>::ctor::cons_(
        std::visit(Overloaded{[](const typename Sig<unsigned int>::exist _args)
                                  -> auto {
                     auto a = _args._a0;
                     return a;
                   }},
                   positive_succ(k_)->v()),
        positives_up_to(k_));
  }
}
