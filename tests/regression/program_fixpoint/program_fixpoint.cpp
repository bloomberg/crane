#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_fixpoint.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> ProgFix::interleave_func(
    const std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                               std::shared_ptr<List<unsigned int>>>> &x) {
  std::shared_ptr<List<unsigned int>> l1 = x->projT1();
  std::shared_ptr<List<unsigned int>> l2 = x->projT2();
  std::function<std::shared_ptr<List<unsigned int>>(
      std::shared_ptr<List<unsigned int>>, std::shared_ptr<List<unsigned int>>)>
      interleave0 = [](std::shared_ptr<List<unsigned int>> l3,
                       std::shared_ptr<List<unsigned int>> l4) {
        std::unique_ptr<
            Sig<std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                                     std::shared_ptr<List<unsigned int>>>>>>
            y = Sig<
                std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                                     std::shared_ptr<List<unsigned int>>>>>::
                ctor::exist_uptr(SigT<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>::
                                     ctor::existT_(l3, l4));
        return interleave_func(std::visit(
            Overloaded{
                [](const typename Sig<std::shared_ptr<
                       SigT<std::shared_ptr<List<unsigned int>>,
                            std::shared_ptr<List<unsigned int>>>>>::exist _args)
                    -> std::shared_ptr<
                        SigT<std::shared_ptr<List<unsigned int>>,
                             std::shared_ptr<List<unsigned int>>>> {
                  std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                                       std::shared_ptr<List<unsigned int>>>>
                      a = _args._a0;
                  return std::move(a);
                }},
            std::move(y)->v()));
      };
  return [&](void) {
    if (std::move(l1).use_count() == 1 && std::move(l1)->v().index() == 1) {
      auto &_rf = std::get<1>(std::move(l1)->v_mut());
      unsigned int x0 = std::move(_rf._a0);
      std::shared_ptr<List<unsigned int>> xs = std::move(_rf._a1);
      _rf._a0 = std::move(x0);
      _rf._a1 = std::move(interleave0)(l2, xs);
      return std::move(l1);
    } else {
      return std::visit(
          Overloaded{[&](const typename List<unsigned int>::nil _args)
                         -> std::shared_ptr<List<unsigned int>> {
                       return std::move(l2);
                     },
                     [&](const typename List<unsigned int>::cons _args)
                         -> std::shared_ptr<List<unsigned int>> {
                       unsigned int x0 = _args._a0;
                       std::shared_ptr<List<unsigned int>> xs = _args._a1;
                       return List<unsigned int>::ctor::cons_(
                           std::move(x0),
                           interleave0(std::move(l2), std::move(xs)));
                     }},
          std::move(l1)->v());
    }
  }();
}

std::shared_ptr<List<unsigned int>>
ProgFix::interleave(std::shared_ptr<List<unsigned int>> l1,
                    std::shared_ptr<List<unsigned int>> l2) {
  return interleave_func(
      SigT<std::shared_ptr<List<unsigned int>>,
           std::shared_ptr<List<unsigned int>>>::ctor::existT_(std::move(l1),
                                                               std::move(l2)));
}
