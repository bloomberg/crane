#include <stack_ops.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure))
std::pair<std::optional<unsigned int>, std::shared_ptr<StackOps::state_basic>>
StackOps::pop_stack(std::shared_ptr<StackOps::state_basic> s) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args)
              -> std::pair<std::optional<unsigned int>,
                           std::shared_ptr<StackOps::state_basic>> {
            return std::make_pair(std::optional<unsigned int>(), std::move(s));
          },
          [](const typename List<unsigned int>::Cons _args)
              -> std::pair<std::optional<unsigned int>,
                           std::shared_ptr<StackOps::state_basic>> {
            return std::make_pair(std::make_optional<unsigned int>(_args.d_a0),
                                  std::make_shared<StackOps::state_basic>(
                                      state_basic{_args.d_a1}));
          }},
      s->stack_basic->v());
}

__attribute__((pure)) bool
StackOps::is_none(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int _x = *o;
    return false;
  } else {
    return true;
  }
}

__attribute__((pure)) unsigned int
StackOps::option_or_zero(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int n = *o;
    return n;
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::pair<std::optional<unsigned int>,
                                std::shared_ptr<StackOps::state_with_acc>>
StackOps::pop_stack_acc(std::shared_ptr<StackOps::state_with_acc> s) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::Nil _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<StackOps::state_with_acc>> {
                   return std::make_pair(std::optional<unsigned int>(),
                                         std::move(s));
                 },
                 [&](const typename List<unsigned int>::Cons _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<StackOps::state_with_acc>> {
                   return std::make_pair(
                       std::make_optional<unsigned int>(_args.d_a0),
                       std::make_shared<StackOps::state_with_acc>(
                           state_with_acc{_args.d_a1, std::move(s)->acc}));
                 }},
      s->stack_with_acc->v());
}

std::shared_ptr<StackOps::state_basic>
StackOps::push_stack(const std::shared_ptr<StackOps::state_basic> &s,
                     const unsigned int addr) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args)
              -> std::shared_ptr<StackOps::state_basic> {
            return std::make_shared<StackOps::state_basic>(
                state_basic{List<unsigned int>::ctor::Cons_(
                    std::move(addr), List<unsigned int>::ctor::Nil_())});
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::shared_ptr<StackOps::state_basic> {
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::Nil _args0)
                        -> std::shared_ptr<StackOps::state_basic> {
                      return std::make_shared<StackOps::state_basic>(
                          state_basic{List<unsigned int>::ctor::Cons_(
                              std::move(addr),
                              List<unsigned int>::ctor::Cons_(
                                  _args.d_a0,
                                  List<unsigned int>::ctor::Nil_()))});
                    },
                    [&](const typename List<unsigned int>::Cons _args0)
                        -> std::shared_ptr<StackOps::state_basic> {
                      return std::visit(
                          Overloaded{
                              [&](const typename List<unsigned int>::Nil _args1)
                                  -> std::shared_ptr<StackOps::state_basic> {
                                return std::make_shared<StackOps::state_basic>(
                                    state_basic{List<unsigned int>::ctor::Cons_(
                                        std::move(addr),
                                        List<unsigned int>::ctor::Cons_(
                                            _args.d_a0,
                                            List<unsigned int>::ctor::Cons_(
                                                _args0.d_a0,
                                                List<unsigned int>::ctor::
                                                    Nil_())))});
                              },
                              [&](const typename List<unsigned int>::Cons
                                      _args1)
                                  -> std::shared_ptr<StackOps::state_basic> {
                                return std::make_shared<StackOps::state_basic>(
                                    state_basic{List<unsigned int>::ctor::Cons_(
                                        std::move(addr),
                                        List<unsigned int>::ctor::Cons_(
                                            _args.d_a0,
                                            List<unsigned int>::ctor::Cons_(
                                                _args0.d_a0,
                                                List<unsigned int>::ctor::
                                                    Nil_())))});
                              }},
                          _args0.d_a1->v());
                    }},
                _args.d_a1->v());
          }},
      s->stack_basic->v());
}

__attribute__((pure)) unsigned int
StackOps::top_or_zero(const std::shared_ptr<StackOps::state_basic> &s) {
  return std::visit(Overloaded{[](const typename List<unsigned int>::Nil _args)
                                   -> unsigned int { return 0u; },
                               [](const typename List<unsigned int>::Cons _args)
                                   -> unsigned int { return _args.d_a0; }},
                    s->stack_basic->v());
}

std::shared_ptr<StackOps::state_basic>
StackOps::push_stack_cap(const std::shared_ptr<StackOps::state_basic> &s,
                         const unsigned int addr) {
  std::shared_ptr<List<unsigned int>> new_stack = std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::Cons_(
                addr, List<unsigned int>::ctor::Nil_());
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::shared_ptr<List<unsigned int>> {
            return std::visit(
                Overloaded{
                    [&](const typename List<unsigned int>::Nil _args0)
                        -> std::shared_ptr<List<unsigned int>> {
                      return List<unsigned int>::ctor::Cons_(
                          addr,
                          List<unsigned int>::ctor::Cons_(
                              _args.d_a0, List<unsigned int>::ctor::Nil_()));
                    },
                    [&](const typename List<unsigned int>::Cons _args0)
                        -> std::shared_ptr<List<unsigned int>> {
                      return std::visit(
                          Overloaded{
                              [&](const typename List<unsigned int>::Nil _args1)
                                  -> std::shared_ptr<List<unsigned int>> {
                                return List<unsigned int>::ctor::Cons_(
                                    addr,
                                    List<unsigned int>::ctor::Cons_(
                                        _args.d_a0,
                                        List<unsigned int>::ctor::Cons_(
                                            _args0.d_a0,
                                            List<unsigned int>::ctor::Nil_())));
                              },
                              [&](const typename List<unsigned int>::Cons
                                      _args1)
                                  -> std::shared_ptr<List<unsigned int>> {
                                return List<unsigned int>::ctor::Cons_(
                                    addr,
                                    List<unsigned int>::ctor::Cons_(
                                        _args.d_a0,
                                        List<unsigned int>::ctor::Cons_(
                                            _args0.d_a0,
                                            List<unsigned int>::ctor::Nil_())));
                              }},
                          _args0.d_a1->v());
                    }},
                _args.d_a1->v());
          }},
      s->stack_basic->v());
  return std::make_shared<StackOps::state_basic>(
      state_basic{std::move(new_stack)});
}
