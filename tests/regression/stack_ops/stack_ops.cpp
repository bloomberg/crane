#include <stack_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure))
std::pair<std::optional<unsigned int>, StackOps::state_basic>
StackOps::pop_stack(StackOps::state_basic s) {
  auto &&_sv = s.stack_basic;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return std::make_pair(std::optional<unsigned int>(), s);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    return std::make_pair(std::make_optional<unsigned int>(d_a0),
                          state_basic{*(d_a1)});
  }
}

__attribute__((pure)) bool
StackOps::is_none(const std::optional<unsigned int> &o) {
  if (o.has_value()) {
    const unsigned int &_x = *o;
    return false;
  } else {
    return true;
  }
}

__attribute__((pure)) unsigned int
StackOps::option_or_zero(const std::optional<unsigned int> &o) {
  if (o.has_value()) {
    const unsigned int &n = *o;
    return n;
  } else {
    return 0u;
  }
}

__attribute__((pure))
std::pair<std::optional<unsigned int>, StackOps::state_with_acc>
StackOps::pop_stack_acc(StackOps::state_with_acc s) {
  auto &&_sv = s.stack_with_acc;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return std::make_pair(std::optional<unsigned int>(), s);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    return std::make_pair(std::make_optional<unsigned int>(d_a0),
                          state_with_acc{*(d_a1), s.acc});
  }
}

__attribute__((pure)) StackOps::state_basic
StackOps::push_stack(const StackOps::state_basic &s, unsigned int addr) {
  auto &&_sv = s.stack_basic;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return state_basic{
        List<unsigned int>::cons(addr, List<unsigned int>::nil())};
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return state_basic{List<unsigned int>::cons(
          addr, List<unsigned int>::cons(d_a0, List<unsigned int>::nil()))};
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      return state_basic{List<unsigned int>::cons(
          addr, List<unsigned int>::cons(
                    d_a0, List<unsigned int>::cons(
                              d_a00, List<unsigned int>::nil())))};
    }
  }
}

__attribute__((pure)) unsigned int
StackOps::top_or_zero(const StackOps::state_basic &s) {
  auto &&_sv = s.stack_basic;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    return d_a0;
  }
}

__attribute__((pure)) StackOps::state_basic
StackOps::push_stack_cap(const StackOps::state_basic &s, unsigned int addr) {
  List<unsigned int> new_stack = [&]() {
    auto &&_sv = s.stack_basic;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
      return List<unsigned int>::cons(addr, List<unsigned int>::nil());
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_sv.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        return List<unsigned int>::cons(
            addr, List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        return List<unsigned int>::cons(
            addr, List<unsigned int>::cons(
                      d_a0, List<unsigned int>::cons(
                                d_a00, List<unsigned int>::nil())));
      }
    }
  }();
  return state_basic{new_stack};
}
