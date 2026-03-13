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
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename NestedInd::expr::Add _args) -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> es =
                _args.d_a0;
            std::function<unsigned int(
                std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                sum_all;
            sum_all =
                [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                -> unsigned int {
              return std::visit(
                  Overloaded{
                      [](const typename List<std::shared_ptr<NestedInd::expr>>::
                             Nil _args) -> unsigned int { return 0u; },
                      [&](const typename List<
                          std::shared_ptr<NestedInd::expr>>::Cons _args)
                          -> unsigned int {
                        std::shared_ptr<NestedInd::expr> e_ = _args.d_a0;
                        std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>
                            rest = _args.d_a1;
                        return (eval(std::move(e_)) + sum_all(std::move(rest)));
                      }},
                  l->v());
            };
            return sum_all(es);
          },
          [](const typename NestedInd::expr::Mul _args) -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> es =
                _args.d_a0;
            std::function<unsigned int(
                std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                prod_all;
            prod_all =
                [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                -> unsigned int {
              return std::visit(
                  Overloaded{
                      [](const typename List<std::shared_ptr<NestedInd::expr>>::
                             Nil _args) -> unsigned int { return 1u; },
                      [&](const typename List<
                          std::shared_ptr<NestedInd::expr>>::Cons _args)
                          -> unsigned int {
                        std::shared_ptr<NestedInd::expr> e_ = _args.d_a0;
                        std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>
                            rest = _args.d_a1;
                        return (eval(std::move(e_)) *
                                prod_all(std::move(rest)));
                      }},
                  l->v());
            };
            return prod_all(es);
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
            std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> es =
                _args.d_a0;
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
                          std::shared_ptr<NestedInd::expr> e_ = _args.d_a0;
                          std::shared_ptr<
                              List<std::shared_ptr<NestedInd::expr>>>
                              rest = _args.d_a1;
                          return (expr_size(std::move(e_)) +
                                  aux(std::move(rest)));
                        }},
                    l->v());
              };
              return aux(es);
            }() + 1);
          },
          [](const typename NestedInd::expr::Mul _args) -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> es =
                _args.d_a0;
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
                          std::shared_ptr<NestedInd::expr> e_ = _args.d_a0;
                          std::shared_ptr<
                              List<std::shared_ptr<NestedInd::expr>>>
                              rest = _args.d_a1;
                          return (expr_size(std::move(e_)) +
                                  aux(std::move(rest)));
                        }},
                    l->v());
              };
              return aux(es);
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
            std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> es =
                _args.d_a0;
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
                          std::shared_ptr<NestedInd::expr> e_ = _args.d_a0;
                          std::shared_ptr<
                              List<std::shared_ptr<NestedInd::expr>>>
                              rest = _args.d_a1;
                          return std::max(expr_depth(std::move(e_)),
                                          aux(std::move(rest)));
                        }},
                    l->v());
              };
              return aux(es);
            }() + 1);
          },
          [](const typename NestedInd::expr::Mul _args) -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> es =
                _args.d_a0;
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
                          std::shared_ptr<NestedInd::expr> e_ = _args.d_a0;
                          std::shared_ptr<
                              List<std::shared_ptr<NestedInd::expr>>>
                              rest = _args.d_a1;
                          return std::max(expr_depth(std::move(e_)),
                                          aux(std::move(rest)));
                        }},
                    l->v());
              };
              return aux(es);
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
            unsigned int n = _args.d_a0;
            return List<unsigned int>::ctor::Cons_(
                std::move(n), List<unsigned int>::ctor::Nil_());
          },
          [](const typename NestedInd::expr::Add _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> es =
                _args.d_a0;
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                aux;
            aux = [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{
                      [](const typename List<std::shared_ptr<NestedInd::expr>>::
                             Nil _args) -> std::shared_ptr<List<unsigned int>> {
                        return List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<NestedInd::expr>>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        std::shared_ptr<NestedInd::expr> e_ = _args.d_a0;
                        std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>
                            rest = _args.d_a1;
                        return literals(std::move(e_))
                            ->app(aux(std::move(rest)));
                      }},
                  l->v());
            };
            return aux(es);
          },
          [](const typename NestedInd::expr::Mul _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> es =
                _args.d_a0;
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>)>
                aux;
            aux = [&](std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>> l)
                -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{
                      [](const typename List<std::shared_ptr<NestedInd::expr>>::
                             Nil _args) -> std::shared_ptr<List<unsigned int>> {
                        return List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<NestedInd::expr>>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        std::shared_ptr<NestedInd::expr> e_ = _args.d_a0;
                        std::shared_ptr<List<std::shared_ptr<NestedInd::expr>>>
                            rest = _args.d_a1;
                        return literals(std::move(e_))
                            ->app(aux(std::move(rest)));
                      }},
                  l->v());
            };
            return aux(es);
          }},
      e->v());
}
