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
  return List<unsigned int>::cons(x, s);
}

__attribute__((pure))
std::optional<std::pair<unsigned int, FunctorComp::Stack::t>>
FunctorComp::Stack::pop(const std::shared_ptr<List<unsigned int>> &s) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(s->v())) {
    return std::optional<
        std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(s->v());
    return std::make_optional<
        std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>(
        std::make_pair(d_a0, d_a1));
  }
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
  const std::shared_ptr<List<unsigned int>> &front = q.first;
  const std::shared_ptr<List<unsigned int>> &back = q.second;
  return std::make_pair(front, List<unsigned int>::cons(x, back));
}

__attribute__((pure))
std::optional<std::pair<unsigned int, FunctorComp::Queue::t>>
FunctorComp::Queue::pop(const std::pair<std::shared_ptr<List<unsigned int>>,
                                        std::shared_ptr<List<unsigned int>>>
                            q) {
  const std::shared_ptr<List<unsigned int>> &front = q.first;
  const std::shared_ptr<List<unsigned int>> &back = q.second;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(front->v())) {
    auto &&_sv0 = back->rev();
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return std::optional<std::pair<
          unsigned int, std::pair<std::shared_ptr<List<unsigned int>>,
                                  std::shared_ptr<List<unsigned int>>>>>();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0->v());
      return std::make_optional<std::pair<
          unsigned int, std::pair<std::shared_ptr<List<unsigned int>>,
                                  std::shared_ptr<List<unsigned int>>>>>(
          std::make_pair(d_a00,
                         std::make_pair(d_a10, List<unsigned int>::nil())));
    }
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(front->v());
    return std::make_optional<std::pair<
        unsigned int, std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>>>(
        std::make_pair(d_a0, std::make_pair(d_a1, back)));
  }
}

__attribute__((pure)) unsigned int
FunctorComp::Queue::size(const std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
                             q) {
  const std::shared_ptr<List<unsigned int>> &front = q.first;
  const std::shared_ptr<List<unsigned int>> &back = q.second;
  return (front->length() + back->length());
}
