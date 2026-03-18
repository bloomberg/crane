#include <function_vernac.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Sig<unsigned int>>
FunctionVernac::div2_terminate(const unsigned int n) {
  if (n <= 0) {
    return Sig<unsigned int>::ctor::Exist_(0u);
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return Sig<unsigned int>::ctor::Exist_(0u);
    } else {
      unsigned int n1 = n0 - 1;
      return std::visit(
          Overloaded{[](const typename Sig<unsigned int>::Exist _args) -> auto {
            return Sig<unsigned int>::ctor::Exist_((_args.d_a0 + 1));
          }},
          div2_terminate(n1)->v());
    }
  }
}

__attribute__((pure)) unsigned int FunctionVernac::div2(const unsigned int n) {
  return std::visit(Overloaded{[](const typename Sig<unsigned int>::Exist _args)
                                   -> unsigned int { return _args.d_a0; }},
                    div2_terminate(n)->v());
}

std::shared_ptr<FunctionVernac::R_div2>
FunctionVernac::R_div2_correct(const unsigned int n, const unsigned int _res) {
  throw std::logic_error("untranslatable curried proof term");
}

std::shared_ptr<Sig<unsigned int>> FunctionVernac::list_sum_terminate(
    const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil _args)
                     -> std::shared_ptr<Sig<unsigned int>> {
                   return Sig<unsigned int>::ctor::Exist_(0u);
                 },
                 [](const typename List<unsigned int>::Cons _args)
                     -> std::shared_ptr<Sig<unsigned int>> {
                   return std::visit(
                       Overloaded{
                           [&](const typename Sig<unsigned int>::Exist _args0)
                               -> auto {
                             return Sig<unsigned int>::ctor::Exist_(
                                 (_args.d_a0 + _args0.d_a0));
                           }},
                       list_sum_terminate(_args.d_a1)->v());
                 }},
      l->v());
}

__attribute__((pure)) unsigned int
FunctionVernac::list_sum(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(Overloaded{[](const typename Sig<unsigned int>::Exist _args)
                                   -> unsigned int { return _args.d_a0; }},
                    list_sum_terminate(l)->v());
}

std::shared_ptr<FunctionVernac::R_list_sum>
FunctionVernac::R_list_sum_correct(const std::shared_ptr<List<unsigned int>> &l,
                                   const unsigned int _res) {
  throw std::logic_error("untranslatable curried proof term");
}
