#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <push_stack.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<PushStack::state>
PushStack::push_stack(const std::shared_ptr<PushStack::state> &s,
                      const unsigned int addr) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::nil _args)
              -> std::shared_ptr<PushStack::state> {
            return std::make_shared<PushStack::state>(
                state{List<unsigned int>::ctor::cons_(
                    std::move(addr), List<unsigned int>::ctor::nil_())});
          },
          [&](const typename List<unsigned int>::cons _args)
              -> std::shared_ptr<PushStack::state> {
            unsigned int x = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::nil _args)
                        -> std::shared_ptr<PushStack::state> {
                      return std::make_shared<PushStack::state>(
                          state{List<unsigned int>::ctor::cons_(
                              std::move(addr),
                              List<unsigned int>::ctor::cons_(
                                  std::move(x),
                                  List<unsigned int>::ctor::nil_()))});
                    },
                    [&](const typename List<unsigned int>::cons _args)
                        -> std::shared_ptr<PushStack::state> {
                      unsigned int y = _args._a0;
                      std::shared_ptr<List<unsigned int>> l0 = _args._a1;
                      return std::visit(
                          Overloaded{
                              [&](const typename List<unsigned int>::nil _args)
                                  -> std::shared_ptr<PushStack::state> {
                                return std::make_shared<PushStack::state>(
                                    state{List<unsigned int>::ctor::cons_(
                                        std::move(addr),
                                        List<unsigned int>::ctor::cons_(
                                            std::move(x),
                                            List<unsigned int>::ctor::cons_(
                                                std::move(y),
                                                List<unsigned int>::ctor::
                                                    nil_())))});
                              },
                              [&](const typename List<unsigned int>::cons _args)
                                  -> std::shared_ptr<PushStack::state> {
                                return std::make_shared<PushStack::state>(
                                    state{List<unsigned int>::ctor::cons_(
                                        std::move(addr),
                                        List<unsigned int>::ctor::cons_(
                                            std::move(x),
                                            List<unsigned int>::ctor::cons_(
                                                std::move(y),
                                                List<unsigned int>::ctor::
                                                    nil_())))});
                              }},
                          std::move(l0)->v());
                    }},
                std::move(l)->v());
          }},
      s->stack->v());
}

unsigned int
PushStack::top_or_zero(const std::shared_ptr<PushStack::state> &s) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args) -> unsigned int {
            return 0u;
          },
          [](const typename List<unsigned int>::cons _args) -> unsigned int {
            unsigned int x = _args._a0;
            return std::move(x);
          }},
      s->stack->v());
}
