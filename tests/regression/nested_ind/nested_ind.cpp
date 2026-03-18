#include <nested_ind.h>

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

std::shared_ptr<NestedInd::rose<unsigned int>>
NestedInd::leaf(const unsigned int n) {
  return rose<unsigned int>::ctor::Node_(
      std::move(n),
      custom_list<
          std::shared_ptr<NestedInd::rose<unsigned int>>>::ctor::Cnil_());
}

__attribute__((pure)) unsigned int
NestedInd::eval(const std::shared_ptr<NestedInd::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename NestedInd::expr::Lit _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename NestedInd::expr::Add _args) -> unsigned int {
            std::function<unsigned int(
                std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                sum_all;
            sum_all =
                [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                -> unsigned int {
              return std::visit(
                  Overloaded{[](const typename List<
                                 std::shared_ptr<NestedInd::expr>>::Nil _args0)
                                 -> unsigned int { return 0u; },
                             [&](const typename List<
                                 std::shared_ptr<NestedInd::expr>>::Cons _args0)
                                 -> unsigned int {
                               return (eval(_args0.d_a0) +
                                       sum_all(_args0.d_a1));
                             }},
                  l->v());
            };
            return sum_all(_args.d_a0);
          },
          [](const typename NestedInd::expr::Mul _args) -> unsigned int {
            std::function<unsigned int(
                std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                prod_all;
            prod_all =
                [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                -> unsigned int {
              return std::visit(
                  Overloaded{[](const typename List<
                                 std::shared_ptr<NestedInd::expr>>::Nil _args0)
                                 -> unsigned int { return 1u; },
                             [&](const typename List<
                                 std::shared_ptr<NestedInd::expr>>::Cons _args0)
                                 -> unsigned int {
                               return (eval(_args0.d_a0) *
                                       prod_all(_args0.d_a1));
                             }},
                  l->v());
            };
            return prod_all(_args.d_a0);
          }},
      e->v());
}

__attribute__((pure)) unsigned int
NestedInd::expr_size(const std::shared_ptr<NestedInd::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename NestedInd::expr::Lit _args) -> unsigned int {
            return 1u;
          },
          [](const typename NestedInd::expr::Add _args) -> unsigned int {
            return ([&](void) {
              std::function<unsigned int(
                  std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                  aux;
              aux =
                  [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                  -> unsigned int {
                return std::visit(
                    Overloaded{
                        [](const typename List<
                            std::shared_ptr<NestedInd::expr>>::Nil _args)
                            -> unsigned int { return 0u; },
                        [&](const typename List<
                            std::shared_ptr<NestedInd::expr>>::Cons _args)
                            -> unsigned int {
                          return (expr_size(_args.d_a0) + aux(_args.d_a1));
                        }},
                    l->v());
              };
              return aux(_args.d_a0);
            }() + 1);
          },
          [](const typename NestedInd::expr::Mul _args) -> unsigned int {
            return ([&](void) {
              std::function<unsigned int(
                  std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                  aux;
              aux =
                  [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                  -> unsigned int {
                return std::visit(
                    Overloaded{
                        [](const typename List<
                            std::shared_ptr<NestedInd::expr>>::Nil _args)
                            -> unsigned int { return 0u; },
                        [&](const typename List<
                            std::shared_ptr<NestedInd::expr>>::Cons _args)
                            -> unsigned int {
                          return (expr_size(_args.d_a0) + aux(_args.d_a1));
                        }},
                    l->v());
              };
              return aux(_args.d_a0);
            }() + 1);
          }},
      e->v());
}

__attribute__((pure)) unsigned int
NestedInd::expr_depth(const std::shared_ptr<NestedInd::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename NestedInd::expr::Lit _args) -> unsigned int {
            return 0u;
          },
          [](const typename NestedInd::expr::Add _args) -> unsigned int {
            return ([&](void) {
              std::function<unsigned int(
                  std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                  aux;
              aux =
                  [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                  -> unsigned int {
                return std::visit(
                    Overloaded{
                        [](const typename List<
                            std::shared_ptr<NestedInd::expr>>::Nil _args)
                            -> unsigned int { return 0u; },
                        [&](const typename List<
                            std::shared_ptr<NestedInd::expr>>::Cons _args)
                            -> unsigned int {
                          return std::max(expr_depth(_args.d_a0),
                                          aux(_args.d_a1));
                        }},
                    l->v());
              };
              return aux(_args.d_a0);
            }() + 1);
          },
          [](const typename NestedInd::expr::Mul _args) -> unsigned int {
            return ([&](void) {
              std::function<unsigned int(
                  std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                  aux;
              aux =
                  [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                  -> unsigned int {
                return std::visit(
                    Overloaded{
                        [](const typename List<
                            std::shared_ptr<NestedInd::expr>>::Nil _args)
                            -> unsigned int { return 0u; },
                        [&](const typename List<
                            std::shared_ptr<NestedInd::expr>>::Cons _args)
                            -> unsigned int {
                          return std::max(expr_depth(_args.d_a0),
                                          aux(_args.d_a1));
                        }},
                    l->v());
              };
              return aux(_args.d_a0);
            }() + 1);
          }},
      e->v());
}

std::shared_ptr<List<unsigned int>>
NestedInd::literals(const std::shared_ptr<NestedInd::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename NestedInd::expr::Lit _args)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::Cons_(
                _args.d_a0, List<unsigned int>::ctor::Nil_());
          },
          [](const typename NestedInd::expr::Add _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                aux;
            aux = [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<NestedInd::expr>>::Nil _args0)
                          -> std::shared_ptr<List<unsigned int>> {
                        return List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<NestedInd::expr>>::Cons _args0)
                          -> std::shared_ptr<List<unsigned int>> {
                        return literals(_args0.d_a0)->app(aux(_args0.d_a1));
                      }},
                  l->v());
            };
            return aux(_args.d_a0);
          },
          [](const typename NestedInd::expr::Mul _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                aux;
            aux = [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<NestedInd::expr>>::Nil _args0)
                          -> std::shared_ptr<List<unsigned int>> {
                        return List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<NestedInd::expr>>::Cons _args0)
                          -> std::shared_ptr<List<unsigned int>> {
                        return literals(_args0.d_a0)->app(aux(_args0.d_a1));
                      }},
                  l->v());
            };
            return aux(_args.d_a0);
          }},
      e->v());
}
