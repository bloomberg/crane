#include "functor_comp.h"

FunctorComp::Stack::t FunctorComp::Stack::push(uint64_t x, List<uint64_t> s) {
  return List<uint64_t>::cons(x, std::move(s));
}

std::optional<std::pair<uint64_t, FunctorComp::Stack::t>>
FunctorComp::Stack::pop(const List<uint64_t> &s) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(s.v())) {
    return std::optional<std::pair<uint64_t, List<uint64_t>>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(s.v());
    return std::make_optional<std::pair<uint64_t, List<uint64_t>>>(
        std::make_pair(a0, *a1));
  }
}

uint64_t FunctorComp::Stack::size(FunctorComp::Stack::t _x0) {
  return _x0.length();
}

FunctorComp::Queue::t
FunctorComp::Queue::push(uint64_t x,
                         const std::pair<List<uint64_t>, List<uint64_t>> &q) {
  const List<uint64_t> &front = q.first;
  const List<uint64_t> &back = q.second;
  return std::make_pair(front, List<uint64_t>::cons(x, back));
}

std::optional<std::pair<uint64_t, FunctorComp::Queue::t>>
FunctorComp::Queue::pop(const std::pair<List<uint64_t>, List<uint64_t>> &q) {
  const List<uint64_t> &front = q.first;
  const List<uint64_t> &back = q.second;
  if (std::holds_alternative<typename List<uint64_t>::Nil>(front.v())) {
    auto &&_sv0 = back.rev();
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return std::optional<
          std::pair<uint64_t, std::pair<List<uint64_t>, List<uint64_t>>>>();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<uint64_t, std::pair<List<uint64_t>, List<uint64_t>>>>(
          std::make_pair(a00, std::make_pair(*a10, List<uint64_t>::nil())));
    }
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(front.v());
    return std::make_optional<
        std::pair<uint64_t, std::pair<List<uint64_t>, List<uint64_t>>>>(
        std::make_pair(a0, std::make_pair(*a1, back)));
  }
}

uint64_t
FunctorComp::Queue::size(const std::pair<List<uint64_t>, List<uint64_t>> &q) {
  const List<uint64_t> &front = q.first;
  const List<uint64_t> &back = q.second;
  return (front.length() + back.length());
}
