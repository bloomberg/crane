#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <push_stack_overflow_len.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> PushStackOverflowLen::stack(
    const std::shared_ptr<PushStackOverflowLen::state> &s) {
  return s->stack;
}

std::shared_ptr<PushStackOverflowLen::state> PushStackOverflowLen::push_stack(
    const std::shared_ptr<PushStackOverflowLen::state> &s,
    const unsigned int addr) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::nil _args)
              -> std::shared_ptr<PushStackOverflowLen::state> {
            return std::make_shared<PushStackOverflowLen::state>(
                state{List<unsigned int>::ctor::cons_(
                    std::move(addr), List<unsigned int>::ctor::nil_())});
          },
          [&](const typename List<unsigned int>::cons _args)
              -> std::shared_ptr<PushStackOverflowLen::state> {
            unsigned int x = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::nil _args)
                        -> std::shared_ptr<PushStackOverflowLen::state> {
                      return std::make_shared<PushStackOverflowLen::state>(
                          state{List<unsigned int>::ctor::cons_(
                              std::move(addr),
                              List<unsigned int>::ctor::cons_(
                                  std::move(x),
                                  List<unsigned int>::ctor::nil_()))});
                    },
                    [&](const typename List<unsigned int>::cons _args)
                        -> std::shared_ptr<PushStackOverflowLen::state> {
                      unsigned int y = _args._a0;
                      std::shared_ptr<List<unsigned int>> l0 = _args._a1;
                      return std::visit(
                          Overloaded{
                              [&](const typename List<unsigned int>::nil _args)
                                  -> std::shared_ptr<
                                      PushStackOverflowLen::state> {
                                return std::make_shared<
                                    PushStackOverflowLen::state>(
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
                                  -> std::shared_ptr<
                                      PushStackOverflowLen::state> {
                                return std::make_shared<
                                    PushStackOverflowLen::state>(
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
