#include <functor_comp.h>

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

__attribute__((pure)) FunctorComp::Stack::t
FunctorComp::Stack::push(const unsigned int x,
                         std::shared_ptr<List<unsigned int>> s) {
  return List<unsigned int>::ctor::Cons_(std::move(x), std::move(s));
}

__attribute__((pure))
std::optional<std::pair<unsigned int, FunctorComp::Stack::t>>
FunctorComp::Stack::pop(const std::shared_ptr<List<unsigned int>> &s) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<unsigned int,
                                         std::shared_ptr<List<unsigned int>>>> {
            return std::nullopt;
          },
          [](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<unsigned int,
                                         std::shared_ptr<List<unsigned int>>>> {
            unsigned int x = _args.d_a0;
            std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
            return std::make_optional<
                std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>(
                std::make_pair(std::move(x), std::move(rest)));
          }},
      s->v());
}

__attribute__((pure)) unsigned int
FunctorComp::Stack::size(const FunctorComp::Stack::t _x0) {
  return _x0->length();
}

__attribute__((pure)) FunctorComp::Queue::t
FunctorComp::Queue::push(const unsigned int x,
                         const std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
                             q) {
  std::shared_ptr<List<unsigned int>> front = q.first;
  std::shared_ptr<List<unsigned int>> back = q.second;
  return std::make_pair(std::move(front),
                        List<unsigned int>::ctor::Cons_(x, back));
}

__attribute__((pure))
std::optional<std::pair<unsigned int, FunctorComp::Queue::t>>
FunctorComp::Queue::pop(const std::pair<std::shared_ptr<List<unsigned int>>,
                                        std::shared_ptr<List<unsigned int>>>
                            q) {
  std::shared_ptr<List<unsigned int>> front = q.first;
  std::shared_ptr<List<unsigned int>> back = q.second;
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args)
              -> std::optional<
                  std::pair<unsigned int,
                            std::pair<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>> {
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::Nil _args)
                        -> std::optional<std::pair<
                            unsigned int,
                            std::pair<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>> {
                      return std::nullopt;
                    },
                    [](const typename List<unsigned int>::Cons _args)
                        -> std::optional<std::pair<
                            unsigned int,
                            std::pair<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>> {
                      unsigned int x = _args.d_a0;
                      std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
                      return std::make_optional<std::pair<
                          unsigned int,
                          std::pair<std::shared_ptr<List<unsigned int>>,
                                    std::shared_ptr<List<unsigned int>>>>>(
                          std::make_pair(
                              std::move(x),
                              std::make_pair(
                                  std::move(rest),
                                  List<unsigned int>::ctor::Nil_())));
                    }},
                back->rev()->v());
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<
                  std::pair<unsigned int,
                            std::pair<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>> {
            unsigned int x = _args.d_a0;
            std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
            return std::make_optional<std::pair<
                unsigned int, std::pair<std::shared_ptr<List<unsigned int>>,
                                        std::shared_ptr<List<unsigned int>>>>>(
                std::make_pair(std::move(x),
                               std::make_pair(std::move(rest), back)));
          }},
      front->v());
}

__attribute__((pure)) unsigned int
FunctorComp::Queue::size(const std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
                             q) {
  std::shared_ptr<List<unsigned int>> front = q.first;
  std::shared_ptr<List<unsigned int>> back = q.second;
  return (front->length() + back->length());
}
