#include "stack_ops.h"

std::pair<std::optional<uint64_t>, StackOps::state_basic>
StackOps::pop_stack(StackOps::state_basic s) {
  auto &&_sv = s.stack_basic;
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::make_pair(std::optional<uint64_t>(), std::move(s));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    return std::make_pair(std::make_optional<uint64_t>(a0), state_basic{*a1});
  }
}

bool StackOps::is_none(const std::optional<uint64_t> &o) {
  if (o.has_value()) {
    const uint64_t &_x = *o;
    return false;
  } else {
    return true;
  }
}

uint64_t StackOps::option_or_zero(const std::optional<uint64_t> &o) {
  if (o.has_value()) {
    const uint64_t &n = *o;
    return n;
  } else {
    return UINT64_C(0);
  }
}

std::pair<std::optional<uint64_t>, StackOps::state_with_acc>
StackOps::pop_stack_acc(StackOps::state_with_acc s) {
  auto &&_sv = s.stack_with_acc;
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::make_pair(std::optional<uint64_t>(), std::move(s));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    return std::make_pair(std::make_optional<uint64_t>(a0),
                          state_with_acc{*a1, s.acc});
  }
}

StackOps::state_basic StackOps::push_stack(const StackOps::state_basic &s,
                                           uint64_t addr) {
  auto &&_sv = s.stack_basic;
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return state_basic{List<uint64_t>::cons(addr, List<uint64_t>::nil())};
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return state_basic{List<uint64_t>::cons(
          addr, List<uint64_t>::cons(a0, List<uint64_t>::nil()))};
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return state_basic{List<uint64_t>::cons(
          addr, List<uint64_t>::cons(
                    a0, List<uint64_t>::cons(a00, List<uint64_t>::nil())))};
    }
  }
}

uint64_t StackOps::top_or_zero(const StackOps::state_basic &s) {
  auto &&_sv = s.stack_basic;
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    return a0;
  }
}

StackOps::state_basic StackOps::push_stack_cap(const StackOps::state_basic &s,
                                               uint64_t addr) {
  List<uint64_t> new_stack = [&]() {
    auto &&_sv = s.stack_basic;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
      return List<uint64_t>::cons(addr, List<uint64_t>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        return List<uint64_t>::cons(
            addr, List<uint64_t>::cons(a0, List<uint64_t>::nil()));
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        return List<uint64_t>::cons(
            addr, List<uint64_t>::cons(
                      a0, List<uint64_t>::cons(a00, List<uint64_t>::nil())));
      }
    }
  }();
  return state_basic{new_stack};
}
