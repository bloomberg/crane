#include <algorithm>
#include <any>
#include <cassert>
#include <func_vernac.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Sig0<unsigned int>>
FuncVernac::div2_terminate(const unsigned int n) {
  if (n <= 0) {
    return Sig0<unsigned int>::ctor::exist_(0);
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return Sig0<unsigned int>::ctor::exist_(0);
    } else {
      unsigned int n1 = n0 - 1;
      return std::visit(
          Overloaded{[](const typename Sig0<T1>::exist _args) -> auto {
            T1 x = _args._a0;
            return Sig0<unsigned int>::ctor::exist_((x + 1));
          }},
          div2_terminate(n1)->v());
    }
  }
}

unsigned int FuncVernac::div2(const unsigned int n) {
  return std::visit(
      Overloaded{
          [](const typename Sig0<unsigned int>::exist _args) -> unsigned int {
            unsigned int a = _args._a0;
            return std::move(a);
          }},
      div2_terminate(n)->v());
}

std::shared_ptr<FuncVernac::R_div2>
FuncVernac::R_div2_correct(const unsigned int n, const unsigned int _res) {
  return div2_rect(
      [](unsigned int y, unsigned int _x0) {
        return R_div2::ctor::R_div2_0_(y);
      },
      [](unsigned int y, unsigned int _x0) {
        return R_div2::ctor::R_div2_1_(y);
      },
      [](unsigned int y, unsigned int y0,
         std::function<std::shared_ptr<FuncVernac::R_div2>(unsigned int,
                                                           dummy_prop)>
             y2,
         unsigned int _x0) {
        return R_div2::ctor::R_div2_2_(y, y0, div2(y0), y2(div2(y0)));
      },
      n, _res, ([&]() -> auto { throw std::logic_error("unreachable"); })());
}

std::shared_ptr<Sig0<unsigned int>>
FuncVernac::list_sum_terminate(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::function<std::shared_ptr<Sig0<unsigned int>>(
                  dummy_prop)> { return Sig0<unsigned int>::ctor::exist_(0); },
          [](const typename List<unsigned int>::cons _args)
              -> std::function<std::shared_ptr<Sig0<unsigned int>>(
                  dummy_prop)> {
            unsigned int n = _args._a0;
            std::shared_ptr<List<unsigned int>> l0 = _args._a1;
            return std::visit(
                Overloaded{[&](const typename Sig0<T1>::exist _args) -> auto {
                  T1 x = _args._a0;
                  return Sig0<unsigned int>::ctor::exist_((std::move(n) + x));
                }},
                list_sum_terminate(std::move(l0))->v());
          }},
      l->v());
}

unsigned int
FuncVernac::list_sum(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename Sig0<unsigned int>::exist _args) -> unsigned int {
            unsigned int a = _args._a0;
            return std::move(a);
          }},
      list_sum_terminate(l)->v());
}

std::shared_ptr<FuncVernac::R_list_sum>
FuncVernac::R_list_sum_correct(const std::shared_ptr<List<unsigned int>> &l,
                               const unsigned int _res) {
  return list_sum_rect(
      [](std::shared_ptr<List<unsigned int>> y, unsigned int _x0) {
        return R_list_sum::ctor::R_list_sum_0_(y);
      },
      [](std::shared_ptr<List<unsigned int>> y, unsigned int y0,
         std::shared_ptr<List<unsigned int>> y1,
         std::function<std::shared_ptr<FuncVernac::R_list_sum>(unsigned int,
                                                               dummy_prop)>
             y3,
         unsigned int _x0) {
        return R_list_sum::ctor::R_list_sum_1_(y, y0, y1, list_sum(y1),
                                               y3(list_sum(y1)));
      },
      l, _res, ([&]() -> auto { throw std::logic_error("unreachable"); })());
}
