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
                               std::shared_ptr<List<unsigned int>>>> &_x0) {
  return [&](const std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                                        std::shared_ptr<List<unsigned int>>>>
                 _x0) {
    return Wf::Fix_sub(
        [&](std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                                 std::shared_ptr<List<unsigned int>>>>
                recarg,
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<Sig0<std::shared_ptr<
                    SigT<std::shared_ptr<List<unsigned int>>,
                         std::shared_ptr<List<unsigned int>>>>>>)>
                interleave_) {
          std::shared_ptr<List<unsigned int>> l1 = recarg->projT1();
          std::shared_ptr<List<unsigned int>> l2 = recarg->projT2();
          std::function<std::shared_ptr<List<unsigned int>>(
              std::shared_ptr<List<unsigned int>>,
              std::shared_ptr<List<unsigned int>>)>
              interleave = [&](std::shared_ptr<List<unsigned int>> l3,
                               std::shared_ptr<List<unsigned int>> l4) {
                return interleave_(
                    Sig0<std::shared_ptr<
                        SigT<std::shared_ptr<List<unsigned int>>,
                             std::shared_ptr<List<unsigned int>>>>>::ctor::
                        exist_(SigT<std::shared_ptr<List<unsigned int>>,
                                    std::shared_ptr<List<unsigned int>>>::ctor::
                                   existT_(l3, l4)));
              };
          return [&](void) {
            if (std::move(l1).use_count() == 1 &&
                std::move(l1)->v().index() == 1) {
              auto &_rf = std::get<1>(std::move(l1)->v_mut());
              std::shared_ptr<List<unsigned int>> xs = std::move(_rf._a0);
              unsigned int x = std::move(_rf._a1);
              _rf._a0 = std::move(x);
              _rf._a1 = std::move(interleave0)(l2, xs);
              return std::move(l1);
            } else {
              return std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::nil _args)
                          -> std::function<std::shared_ptr<List<unsigned int>>(
                              dummy_prop)> { return std::move(l2); },
                      [&](const typename List<unsigned int>::cons _args)
                          -> std::function<std::shared_ptr<List<unsigned int>>(
                              dummy_prop)> {
                        unsigned int x = _args._a0;
                        std::shared_ptr<List<unsigned int>> xs = _args._a1;
                        return List<unsigned int>::ctor::cons_(
                            std::move(x),
                            interleave0(std::move(l2), std::move(xs)));
                      }},
                  std::move(l1)->v());
            }
          }();
        },
        _x0);
  }(_x0);
}

std::shared_ptr<List<unsigned int>>
ProgFix::interleave(std::shared_ptr<List<unsigned int>> l1,
                    std::shared_ptr<List<unsigned int>> l2) {
  return interleave_func(
      SigT<std::shared_ptr<List<unsigned int>>,
           std::shared_ptr<List<unsigned int>>>::ctor::existT_(std::move(l1),
                                                               std::move(l2)));
}
