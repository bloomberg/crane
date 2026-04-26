#include <name_clash_scope_leak.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Match on list, return list. Both branches produce the same type.
__attribute__((pure)) List<unsigned int>
NameClashScopeLeak::rotate(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return (*(d_a1)).app(
        List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
  }
}

/// Two consecutive matches on different lists in the same function.
__attribute__((pure)) unsigned int
NameClashScopeLeak::heads_sum(const List<unsigned int> &l1,
                              const List<unsigned int> &l2) {
  unsigned int h1 = [&]() {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l1.v());
      return d_a0;
    }
  }();
  unsigned int h2 = [&]() {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(l2.v());
      return d_a00;
    }
  }();
  return (h1 + h2);
}

/// Match on list, and in the Cons branch, match on the tail.
__attribute__((pure)) unsigned int
NameClashScopeLeak::first_two_sum(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return d_a0;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      return (d_a0 + d_a00);
    }
  }
}

/// Match where both branches contain let bindings with same name.
__attribute__((pure)) unsigned int
NameClashScopeLeak::branch_let_clash(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return (d_a0 * 2u);
  }
}

/// Three consecutive matches, each with same binding variable name pattern.
__attribute__((pure)) unsigned int
NameClashScopeLeak::triple_head(const List<unsigned int> &l1,
                                const List<unsigned int> &l2,
                                const List<unsigned int> &l3) {
  unsigned int a = [&]() {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l1.v());
      return d_a0;
    }
  }();
  unsigned int b = [&]() {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(l2.v());
      return d_a00;
    }
  }();
  unsigned int c = [&]() {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l3.v())) {
      return 0u;
    } else {
      const auto &[d_a01, d_a11] =
          std::get<typename List<unsigned int>::Cons>(l3.v());
      return d_a01;
    }
  }();
  return ((a + b) + c);
}

/// Matching on a pair where both components are lists.
__attribute__((pure)) unsigned int NameClashScopeLeak::pair_match(
    const std::pair<List<unsigned int>, List<unsigned int>> &p) {
  const List<unsigned int> &l1 = p.first;
  const List<unsigned int> &l2 = p.second;
  unsigned int h1 = [&]() {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l1.v());
      return d_a0;
    }
  }();
  unsigned int h2 = [&]() {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(l2.v());
      return d_a00;
    }
  }();
  return (h1 + h2);
}
