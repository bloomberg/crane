#include <functor_comp.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) FunctorComp::Stack::t
FunctorComp::Stack::push(const unsigned int x,
                         std::shared_ptr<List<unsigned int>> s) {
  return List<unsigned int>::cons(std::move(x), std::move(s));
}

__attribute__((pure))
std::optional<std::pair<unsigned int, FunctorComp::Stack::t>>
FunctorComp::Stack::pop(const std::shared_ptr<List<unsigned int>> &s) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<unsigned int,
                                         std::shared_ptr<List<unsigned int>>>> {
            return std::optional<
                std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>();
          },
          [](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<unsigned int,
                                         std::shared_ptr<List<unsigned int>>>> {
            return std::make_optional<
                std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>(
                std::make_pair(_args.d_a0, _args.d_a1));
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
  return std::make_pair(std::move(front), List<unsigned int>::cons(x, back));
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
                    [](const typename List<unsigned int>::Nil _args0)
                        -> std::optional<std::pair<
                            unsigned int,
                            std::pair<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>> {
                      return std::optional<std::pair<
                          unsigned int,
                          std::pair<std::shared_ptr<List<unsigned int>>,
                                    std::shared_ptr<List<unsigned int>>>>>();
                    },
                    [](const typename List<unsigned int>::Cons _args0)
                        -> std::optional<std::pair<
                            unsigned int,
                            std::pair<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>> {
                      return std::make_optional<std::pair<
                          unsigned int,
                          std::pair<std::shared_ptr<List<unsigned int>>,
                                    std::shared_ptr<List<unsigned int>>>>>(
                          std::make_pair(
                              _args0.d_a0,
                              std::make_pair(_args0.d_a1,
                                             List<unsigned int>::nil())));
                    }},
                back->rev()->v());
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<
                  std::pair<unsigned int,
                            std::pair<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>> {
            return std::make_optional<std::pair<
                unsigned int, std::pair<std::shared_ptr<List<unsigned int>>,
                                        std::shared_ptr<List<unsigned int>>>>>(
                std::make_pair(_args.d_a0, std::make_pair(_args.d_a1, back)));
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
