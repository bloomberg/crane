#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nested_ind_stdlib_list.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
NestedIndStdlibList::eval(const std::shared_ptr<NestedIndStdlibList::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename NestedIndStdlibList::expr::Lit _args)
              -> unsigned int {
            unsigned int n = _args._a0;
            return std::move(n);
          },
          [](const typename NestedIndStdlibList::expr::Add _args)
              -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedIndStdlibList::expr>>>
                es = _args._a0;
            std::function<unsigned int(
                std::shared_ptr<
                    List<std::shared_ptr<NestedIndStdlibList::expr>>>)>
                sum_all;
            sum_all = [&](std::shared_ptr<
                          List<std::shared_ptr<NestedIndStdlibList::expr>>>
                              l) -> unsigned int {
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<NestedIndStdlibList::expr>>::nil
                             _args) -> unsigned int { return 0u; },
                      [&](const typename List<
                          std::shared_ptr<NestedIndStdlibList::expr>>::cons
                              _args) -> unsigned int {
                        std::shared_ptr<NestedIndStdlibList::expr> e_ =
                            _args._a0;
                        std::shared_ptr<
                            List<std::shared_ptr<NestedIndStdlibList::expr>>>
                            rest = _args._a1;
                        return (eval(std::move(e_)) + sum_all(std::move(rest)));
                      }},
                  l->v());
            };
            return sum_all(es);
          },
          [](const typename NestedIndStdlibList::expr::Mul _args)
              -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedIndStdlibList::expr>>>
                es = _args._a0;
            std::function<unsigned int(
                std::shared_ptr<
                    List<std::shared_ptr<NestedIndStdlibList::expr>>>)>
                prod_all;
            prod_all = [&](std::shared_ptr<
                           List<std::shared_ptr<NestedIndStdlibList::expr>>>
                               l) -> unsigned int {
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<NestedIndStdlibList::expr>>::nil
                             _args) -> unsigned int { return 1u; },
                      [&](const typename List<
                          std::shared_ptr<NestedIndStdlibList::expr>>::cons
                              _args) -> unsigned int {
                        std::shared_ptr<NestedIndStdlibList::expr> e_ =
                            _args._a0;
                        std::shared_ptr<
                            List<std::shared_ptr<NestedIndStdlibList::expr>>>
                            rest = _args._a1;
                        return (eval(std::move(e_)) *
                                prod_all(std::move(rest)));
                      }},
                  l->v());
            };
            return prod_all(es);
          }},
      e->v());
}

unsigned int NestedIndStdlibList::expr_size(
    const std::shared_ptr<NestedIndStdlibList::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename NestedIndStdlibList::expr::Lit _args)
              -> unsigned int { return 1u; },
          [](const typename NestedIndStdlibList::expr::Add _args)
              -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedIndStdlibList::expr>>>
                es = _args._a0;
            return ([&](void) {
              std::function<unsigned int(
                  std::shared_ptr<
                      List<std::shared_ptr<NestedIndStdlibList::expr>>>)>
                  aux;
              aux = [&](std::shared_ptr<
                        List<std::shared_ptr<NestedIndStdlibList::expr>>>
                            l) -> unsigned int {
                return std::visit(
                    Overloaded{
                        [](const typename List<
                            std::shared_ptr<NestedIndStdlibList::expr>>::nil
                               _args) -> unsigned int { return 0u; },
                        [&](const typename List<
                            std::shared_ptr<NestedIndStdlibList::expr>>::cons
                                _args) -> unsigned int {
                          std::shared_ptr<NestedIndStdlibList::expr> e_ =
                              _args._a0;
                          std::shared_ptr<
                              List<std::shared_ptr<NestedIndStdlibList::expr>>>
                              rest = _args._a1;
                          return (expr_size(std::move(e_)) +
                                  aux(std::move(rest)));
                        }},
                    l->v());
              };
              return aux(es);
            }() + 1);
          },
          [](const typename NestedIndStdlibList::expr::Mul _args)
              -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedIndStdlibList::expr>>>
                es = _args._a0;
            return ([&](void) {
              std::function<unsigned int(
                  std::shared_ptr<
                      List<std::shared_ptr<NestedIndStdlibList::expr>>>)>
                  aux;
              aux = [&](std::shared_ptr<
                        List<std::shared_ptr<NestedIndStdlibList::expr>>>
                            l) -> unsigned int {
                return std::visit(
                    Overloaded{
                        [](const typename List<
                            std::shared_ptr<NestedIndStdlibList::expr>>::nil
                               _args) -> unsigned int { return 0u; },
                        [&](const typename List<
                            std::shared_ptr<NestedIndStdlibList::expr>>::cons
                                _args) -> unsigned int {
                          std::shared_ptr<NestedIndStdlibList::expr> e_ =
                              _args._a0;
                          std::shared_ptr<
                              List<std::shared_ptr<NestedIndStdlibList::expr>>>
                              rest = _args._a1;
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

unsigned int NestedIndStdlibList::expr_depth(
    const std::shared_ptr<NestedIndStdlibList::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename NestedIndStdlibList::expr::Lit _args)
              -> unsigned int { return 0u; },
          [](const typename NestedIndStdlibList::expr::Add _args)
              -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedIndStdlibList::expr>>>
                es = _args._a0;
            return ([&](void) {
              std::function<unsigned int(
                  std::shared_ptr<
                      List<std::shared_ptr<NestedIndStdlibList::expr>>>)>
                  aux;
              aux = [&](std::shared_ptr<
                        List<std::shared_ptr<NestedIndStdlibList::expr>>>
                            l) -> unsigned int {
                return std::visit(
                    Overloaded{
                        [](const typename List<
                            std::shared_ptr<NestedIndStdlibList::expr>>::nil
                               _args) -> unsigned int { return 0u; },
                        [&](const typename List<
                            std::shared_ptr<NestedIndStdlibList::expr>>::cons
                                _args) -> unsigned int {
                          std::shared_ptr<NestedIndStdlibList::expr> e_ =
                              _args._a0;
                          std::shared_ptr<
                              List<std::shared_ptr<NestedIndStdlibList::expr>>>
                              rest = _args._a1;
                          return std::max(expr_depth(std::move(e_)),
                                          aux(std::move(rest)));
                        }},
                    l->v());
              };
              return aux(es);
            }() + 1);
          },
          [](const typename NestedIndStdlibList::expr::Mul _args)
              -> unsigned int {
            std::shared_ptr<List<std::shared_ptr<NestedIndStdlibList::expr>>>
                es = _args._a0;
            return ([&](void) {
              std::function<unsigned int(
                  std::shared_ptr<
                      List<std::shared_ptr<NestedIndStdlibList::expr>>>)>
                  aux;
              aux = [&](std::shared_ptr<
                        List<std::shared_ptr<NestedIndStdlibList::expr>>>
                            l) -> unsigned int {
                return std::visit(
                    Overloaded{
                        [](const typename List<
                            std::shared_ptr<NestedIndStdlibList::expr>>::nil
                               _args) -> unsigned int { return 0u; },
                        [&](const typename List<
                            std::shared_ptr<NestedIndStdlibList::expr>>::cons
                                _args) -> unsigned int {
                          std::shared_ptr<NestedIndStdlibList::expr> e_ =
                              _args._a0;
                          std::shared_ptr<
                              List<std::shared_ptr<NestedIndStdlibList::expr>>>
                              rest = _args._a1;
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

std::shared_ptr<List<unsigned int>> NestedIndStdlibList::literals(
    const std::shared_ptr<NestedIndStdlibList::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename NestedIndStdlibList::expr::Lit _args)
              -> std::shared_ptr<List<unsigned int>> {
            unsigned int n = _args._a0;
            return List<unsigned int>::ctor::cons_(
                std::move(n), List<unsigned int>::ctor::nil_());
          },
          [](const typename NestedIndStdlibList::expr::Add _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<List<std::shared_ptr<NestedIndStdlibList::expr>>>
                es = _args._a0;
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<
                    List<std::shared_ptr<NestedIndStdlibList::expr>>>)>
                aux;
            aux = [&](std::shared_ptr<
                      List<std::shared_ptr<NestedIndStdlibList::expr>>>
                          l) -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<NestedIndStdlibList::expr>>::nil
                             _args) -> std::shared_ptr<List<unsigned int>> {
                        return List<unsigned int>::ctor::nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<NestedIndStdlibList::expr>>::cons
                              _args) -> std::shared_ptr<List<unsigned int>> {
                        std::shared_ptr<NestedIndStdlibList::expr> e_ =
                            _args._a0;
                        std::shared_ptr<
                            List<std::shared_ptr<NestedIndStdlibList::expr>>>
                            rest = _args._a1;
                        return literals(std::move(e_))
                            ->app(aux(std::move(rest)));
                      }},
                  l->v());
            };
            return aux(es);
          },
          [](const typename NestedIndStdlibList::expr::Mul _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<List<std::shared_ptr<NestedIndStdlibList::expr>>>
                es = _args._a0;
            std::function<std::shared_ptr<List<unsigned int>>(
                std::shared_ptr<
                    List<std::shared_ptr<NestedIndStdlibList::expr>>>)>
                aux;
            aux = [&](std::shared_ptr<
                      List<std::shared_ptr<NestedIndStdlibList::expr>>>
                          l) -> std::shared_ptr<List<unsigned int>> {
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<NestedIndStdlibList::expr>>::nil
                             _args) -> std::shared_ptr<List<unsigned int>> {
                        return List<unsigned int>::ctor::nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<NestedIndStdlibList::expr>>::cons
                              _args) -> std::shared_ptr<List<unsigned int>> {
                        std::shared_ptr<NestedIndStdlibList::expr> e_ =
                            _args._a0;
                        std::shared_ptr<
                            List<std::shared_ptr<NestedIndStdlibList::expr>>>
                            rest = _args._a1;
                        return literals(std::move(e_))
                            ->app(aux(std::move(rest)));
                      }},
                  l->v());
            };
            return aux(es);
          }},
      e->v());
}
