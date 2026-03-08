#include <algorithm>
#include <any>
#include <cassert>
#include <function_vernac.h>
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
    return Sig<unsigned int>::ctor::exist_(0u);
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return Sig<unsigned int>::ctor::exist_(0u);
    } else {
      unsigned int n1 = n0 - 1;
      return std::visit(
          Overloaded{[](const typename Sig<unsigned int>::exist _args) -> auto {
            auto x = _args._a0;
            return Sig<unsigned int>::ctor::exist_((x + 1));
          }},
          div2_terminate(n1)->v());
    }
  }
}

unsigned int FunctionVernac::div2(const unsigned int n) {
  return std::visit(
      Overloaded{
          [](const typename Sig<unsigned int>::exist _args) -> unsigned int {
            unsigned int a = _args._a0;
            return std::move(a);
          }},
      div2_terminate(n)->v());
}

std::shared_ptr<FunctionVernac::R_div2>
FunctionVernac::R_div2_correct(const unsigned int n, const unsigned int _res) {
  throw std::logic_error("untranslatable curried proof term");
}

std::shared_ptr<Sig<unsigned int>> FunctionVernac::list_sum_terminate(
    const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::shared_ptr<Sig<unsigned int>> {
            return Sig<unsigned int>::ctor::exist_(0u);
          },
          [](const typename List<unsigned int>::cons _args)
              -> std::shared_ptr<Sig<unsigned int>> {
            unsigned int n = _args._a0;
            std::shared_ptr<List<unsigned int>> l0 = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename Sig<unsigned int>::exist _args) -> auto {
                      auto x = _args._a0;
                      return Sig<unsigned int>::ctor::exist_(
                          (std::move(n) + x));
                    }},
                list_sum_terminate(std::move(l0))->v());
          }},
      l->v());
}

unsigned int
FunctionVernac::list_sum(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename Sig<unsigned int>::exist _args) -> unsigned int {
            unsigned int a = _args._a0;
            return std::move(a);
          }},
      list_sum_terminate(l)->v());
}

std::shared_ptr<FunctionVernac::R_list_sum>
FunctionVernac::R_list_sum_correct(const std::shared_ptr<List<unsigned int>> &l,
                                   const unsigned int _res) {
  throw std::logic_error("untranslatable curried proof term");
}
