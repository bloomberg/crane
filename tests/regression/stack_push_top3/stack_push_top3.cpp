#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stack_push_top3.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>>
StackPushTop3::stack(const std::shared_ptr<StackPushTop3::state> &s) {
  return s->stack;
}

std::shared_ptr<StackPushTop3::state>
StackPushTop3::push_stack(const std::shared_ptr<StackPushTop3::state> &s,
                          const unsigned int addr) {
  std::shared_ptr<List<unsigned int>> new_stack = std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::nil _args)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::cons_(
                std::move(addr), List<unsigned int>::ctor::nil_());
          },
          [&](const typename List<unsigned int>::cons _args)
              -> std::shared_ptr<List<unsigned int>> {
            unsigned int a = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::nil _args)
                        -> std::shared_ptr<List<unsigned int>> {
                      return List<unsigned int>::ctor::cons_(
                          std::move(addr),
                          List<unsigned int>::ctor::cons_(
                              std::move(a), List<unsigned int>::ctor::nil_()));
                    },
                    [&](const typename List<unsigned int>::cons _args)
                        -> std::shared_ptr<List<unsigned int>> {
                      unsigned int b = _args._a0;
                      std::shared_ptr<List<unsigned int>> l0 = _args._a1;
                      return [&](void) {
                        if (std::move(l0).use_count() == 1 &&
                            std::move(l0)->v().index() == 1) {
                          auto &_rf = std::get<1>(std::move(l0)->v_mut());
                          _rf._a0 = addr;
                          _rf._a1 = List<unsigned int>::ctor::cons_(
                              a, List<unsigned int>::ctor::cons_(
                                     std::move(b),
                                     List<unsigned int>::ctor::nil_()));
                          return std::move(l0);
                        } else {
                          return std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::nil
                                          _args)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    return List<unsigned int>::ctor::cons_(
                                        std::move(addr),
                                        List<unsigned int>::ctor::cons_(
                                            std::move(a),
                                            List<unsigned int>::ctor::cons_(
                                                std::move(b),
                                                List<unsigned int>::ctor::
                                                    nil_())));
                                  },
                                  [&](const typename List<unsigned int>::cons
                                          _args)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    return List<unsigned int>::ctor::cons_(
                                        std::move(addr),
                                        List<unsigned int>::ctor::cons_(
                                            std::move(a),
                                            List<unsigned int>::ctor::cons_(
                                                std::move(b),
                                                List<unsigned int>::ctor::
                                                    nil_())));
                                  }},
                              std::move(l0)->v());
                        }
                      }();
                    }},
                std::move(l)->v());
          }},
      s->stack->v());
  return std::make_shared<StackPushTop3::state>(state{std::move(new_stack)});
}
