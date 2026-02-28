#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <functor_comp.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

t FunctorComp::Stack::push(const unsigned int x,
                           std::shared_ptr<List::list<unsigned int>> s) {
  return List::list<unsigned int>::ctor::cons_(std::move(x), std::move(s));
}

std::optional<std::pair<unsigned int, t>>
FunctorComp::Stack::pop(const std::shared_ptr<List::list<unsigned int>> &s) {
  return std::visit(
      Overloaded{
          [](const typename List::list<unsigned int>::nil _args)
              -> std::optional<std::pair<
                  unsigned int, std::shared_ptr<List::list<unsigned int>>>> {
            return std::nullopt;
          },
          [](const typename List::list<unsigned int>::cons _args)
              -> std::optional<std::pair<
                  unsigned int, std::shared_ptr<List::list<unsigned int>>>> {
            unsigned int x = _args._a0;
            std::shared_ptr<List::list<unsigned int>> rest = _args._a1;
            return std::make_optional<std::pair<
                unsigned int, std::shared_ptr<List::list<unsigned int>>>>(
                std::make_pair(std::move(x), std::move(rest)));
          }},
      s->v());
}

unsigned int FunctorComp::Stack::size(const t _x0) { return _x0->length(); }

t FunctorComp::Queue::push(
    const unsigned int x,
    const std::pair<std::shared_ptr<List::list<unsigned int>>,
                    std::shared_ptr<List::list<unsigned int>>>
        q) {
  std::shared_ptr<List::list<unsigned int>> front = q.first;
  std::shared_ptr<List::list<unsigned int>> back = q.second;
  return std::make_pair(std::move(front),
                        List::list<unsigned int>::ctor::cons_(x, back));
}

std::optional<std::pair<unsigned int, t>> FunctorComp::Queue::pop(
    const std::pair<std::shared_ptr<List::list<unsigned int>>,
                    std::shared_ptr<List::list<unsigned int>>>
        q) {
  std::shared_ptr<List::list<unsigned int>> front = q.first;
  std::shared_ptr<List::list<unsigned int>> back = q.second;
  return std::visit(
      Overloaded{
          [&](const typename List::list<unsigned int>::nil _args)
              -> std::optional<std::pair<
                  unsigned int,
                  std::pair<std::shared_ptr<List::list<unsigned int>>,
                            std::shared_ptr<List::list<unsigned int>>>>> {
            return std::visit(
                Overloaded{
                    [](const typename List::list<unsigned int>::nil _args)
                        -> std::optional<std::pair<
                            unsigned int,
                            std::pair<
                                std::shared_ptr<List::list<unsigned int>>,
                                std::shared_ptr<List::list<unsigned int>>>>> {
                      return std::nullopt;
                    },
                    [](const typename List::list<unsigned int>::cons _args)
                        -> std::optional<std::pair<
                            unsigned int,
                            std::pair<
                                std::shared_ptr<List::list<unsigned int>>,
                                std::shared_ptr<List::list<unsigned int>>>>> {
                      unsigned int x = _args._a0;
                      std::shared_ptr<List::list<unsigned int>> rest =
                          _args._a1;
                      return std::make_optional<std::pair<
                          unsigned int,
                          std::pair<
                              std::shared_ptr<List::list<unsigned int>>,
                              std::shared_ptr<List::list<unsigned int>>>>>(
                          std::make_pair(
                              std::move(x),
                              std::make_pair(
                                  std::move(rest),
                                  List::list<unsigned int>::ctor::nil_())));
                    }},
                back->rev()->v());
          },
          [&](const typename List::list<unsigned int>::cons _args)
              -> std::optional<std::pair<
                  unsigned int,
                  std::pair<std::shared_ptr<List::list<unsigned int>>,
                            std::shared_ptr<List::list<unsigned int>>>>> {
            unsigned int x = _args._a0;
            std::shared_ptr<List::list<unsigned int>> rest = _args._a1;
            return std::make_optional<std::pair<
                unsigned int,
                std::pair<std::shared_ptr<List::list<unsigned int>>,
                          std::shared_ptr<List::list<unsigned int>>>>>(
                std::make_pair(std::move(x),
                               std::make_pair(std::move(rest), back)));
          }},
      front->v());
}

unsigned int FunctorComp::Queue::size(
    const std::pair<std::shared_ptr<List::list<unsigned int>>,
                    std::shared_ptr<List::list<unsigned int>>>
        q) {
  std::shared_ptr<List::list<unsigned int>> front = q.first;
  std::shared_ptr<List::list<unsigned int>> back = q.second;
  return (front->length() + back->length());
}
