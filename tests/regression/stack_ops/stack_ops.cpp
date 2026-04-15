#include <stack_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure))
std::pair<std::optional<unsigned int>, std::shared_ptr<StackOps::state_basic>>
StackOps::pop_stack(std::shared_ptr<StackOps::state_basic> s) {
  auto &&_sv = s->stack_basic;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::make_pair(std::optional<unsigned int>(), std::move(s));
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    return std::make_pair(
        std::make_optional<unsigned int>(_m.d_a0),
        std::make_shared<StackOps::state_basic>(state_basic{_m.d_a1}));
  }
}

__attribute__((pure)) bool
StackOps::is_none(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    const unsigned int &_x = *o;
    return false;
  } else {
    return true;
  }
}

__attribute__((pure)) unsigned int
StackOps::option_or_zero(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    const unsigned int &n = *o;
    return n;
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::pair<std::optional<unsigned int>,
                                std::shared_ptr<StackOps::state_with_acc>>
StackOps::pop_stack_acc(std::shared_ptr<StackOps::state_with_acc> s) {
  auto &&_sv = s->stack_with_acc;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::make_pair(std::optional<unsigned int>(), std::move(s));
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    return std::make_pair(std::make_optional<unsigned int>(_m.d_a0),
                          std::make_shared<StackOps::state_with_acc>(
                              state_with_acc{_m.d_a1, s->acc}));
  }
}

std::shared_ptr<StackOps::state_basic>
StackOps::push_stack(const std::shared_ptr<StackOps::state_basic> &s,
                     const unsigned int addr) {
  auto &&_sv = s->stack_basic;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::make_shared<StackOps::state_basic>(
        state_basic{List<unsigned int>::cons(addr, List<unsigned int>::nil())});
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return std::make_shared<StackOps::state_basic>(
          state_basic{List<unsigned int>::cons(
              addr,
              List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil()))});
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      return std::make_shared<StackOps::state_basic>(
          state_basic{List<unsigned int>::cons(
              addr, List<unsigned int>::cons(
                        _m.d_a0, List<unsigned int>::cons(
                                     _m0.d_a0, List<unsigned int>::nil())))});
    }
  }
}

__attribute__((pure)) unsigned int
StackOps::top_or_zero(const std::shared_ptr<StackOps::state_basic> &s) {
  auto &&_sv = s->stack_basic;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    return _m.d_a0;
  }
}

std::shared_ptr<StackOps::state_basic>
StackOps::push_stack_cap(const std::shared_ptr<StackOps::state_basic> &s,
                         const unsigned int addr) {
  std::shared_ptr<List<unsigned int>> new_stack = [&]() {
    auto &&_sv = s->stack_basic;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
      return List<unsigned int>::cons(addr, List<unsigned int>::nil());
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
      auto &&_sv0 = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
        return List<unsigned int>::cons(
            addr, List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil()));
      } else {
        const auto &_m0 =
            *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
        return List<unsigned int>::cons(
            addr, List<unsigned int>::cons(
                      _m.d_a0, List<unsigned int>::cons(
                                   _m0.d_a0, List<unsigned int>::nil())));
      }
    }
  }();
  return std::make_shared<StackOps::state_basic>(state_basic{new_stack});
}
