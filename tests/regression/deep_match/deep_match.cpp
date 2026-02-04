#include <algorithm>
#include <any>
#include <deep_match.h>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int DeepMatch::match_pair_list(
    const std::shared_ptr<DeepMatch::list<
        std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename DeepMatch::list<
              std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>>>::nil
                 _args) -> unsigned int { return 0u; },
          [](const typename DeepMatch::list<std::shared_ptr<
                 DeepMatch::pair<unsigned int, unsigned int>>>::cons _args)
              -> unsigned int {
            std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>> p =
                _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename DeepMatch::pair<unsigned int,
                                                      unsigned int>::Pair _args)
                        -> unsigned int {
                      unsigned int x = _args._a0;
                      return x;
                    }},
                p->v());
          }},
      l->v());
}

unsigned int
DeepMatch::match_two(const std::shared_ptr<DeepMatch::list<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename DeepMatch::list<unsigned int>::nil _args)
              -> unsigned int { return 0u; },
          [](const typename DeepMatch::list<unsigned int>::cons _args)
              -> unsigned int {
            unsigned int x = _args._a0;
            std::shared_ptr<DeepMatch::list<unsigned int>> l0 = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename DeepMatch::list<unsigned int>::nil _args)
                        -> unsigned int { return x; },
                    [&](const typename DeepMatch::list<unsigned int>::cons
                            _args) -> unsigned int { return x; }},
                l0->v());
          }},
      l->v());
}

unsigned int DeepMatch::match_triple(
    const std::shared_ptr<DeepMatch::list<std::shared_ptr<
        DeepMatch::list<std::shared_ptr<DeepMatch::list<unsigned int>>>>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename DeepMatch::list<std::shared_ptr<DeepMatch::list<
                 std::shared_ptr<DeepMatch::list<unsigned int>>>>>::nil _args)
              -> unsigned int { return 0u; },
          [](const typename DeepMatch::list<std::shared_ptr<DeepMatch::list<
                 std::shared_ptr<DeepMatch::list<unsigned int>>>>>::cons _args)
              -> unsigned int {
            std::shared_ptr<
                DeepMatch::list<std::shared_ptr<DeepMatch::list<unsigned int>>>>
                l0 = _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename DeepMatch::list<
                        std::shared_ptr<DeepMatch::list<unsigned int>>>::nil
                           _args) -> unsigned int { return 1u; },
                    [](const typename DeepMatch::list<
                        std::shared_ptr<DeepMatch::list<unsigned int>>>::cons
                           _args) -> unsigned int {
                      std::shared_ptr<DeepMatch::list<unsigned int>> l2 =
                          _args._a0;
                      return std::visit(
                          Overloaded{
                              [](const typename DeepMatch::list<
                                  unsigned int>::nil _args) -> unsigned int {
                                return 2u;
                              },
                              [](const typename DeepMatch::list<
                                  unsigned int>::cons _args) -> unsigned int {
                                unsigned int n = _args._a0;
                                return n;
                              }},
                          l2->v());
                    }},
                l0->v());
          }},
      l->v());
}

unsigned int DeepMatch::deep_wildcard(
    const std::shared_ptr<DeepMatch::pair<
        std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>>,
        std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>>>> &p) {
  return std::visit(
      Overloaded{
          [](const typename DeepMatch::pair<
              std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>>,
              std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>>>::
                 Pair _args) -> unsigned int {
            std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>> p0 =
                _args._a0;
            std::shared_ptr<DeepMatch::pair<unsigned int, unsigned int>> p1 =
                _args._a1;
            return std::visit(
                Overloaded{[&](const typename DeepMatch::pair<
                               unsigned int, unsigned int>::Pair _args)
                               -> unsigned int {
                  unsigned int a = _args._a0;
                  return std::visit(
                      Overloaded{[&](const typename DeepMatch::pair<
                                     unsigned int, unsigned int>::Pair _args)
                                     -> unsigned int { return a; }},
                      p1->v());
                }},
                p0->v());
          }},
      p->v());
}
