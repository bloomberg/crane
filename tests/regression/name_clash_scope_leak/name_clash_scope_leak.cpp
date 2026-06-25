#include "name_clash_scope_leak.h"

/// Match on list, return list. Both branches produce the same type.
List<uint64_t> NameClashScopeLeak::rotate(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a1->app(List<uint64_t>::cons(a0, List<uint64_t>::nil()));
  }
}

/// Two consecutive matches on different lists in the same function.
uint64_t NameClashScopeLeak::heads_sum(const List<uint64_t> &l1,
                                       const List<uint64_t> &l2) {
  uint64_t h1 = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
      return a0;
    }
  }();
  uint64_t h2 = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(l2.v());
      return a00;
    }
  }();
  return (h1 + h2);
}

/// Match on list, and in the Cons branch, match on the tail.
uint64_t NameClashScopeLeak::first_two_sum(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return a0;
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return (a0 + a00);
    }
  }
}

/// Match where both branches contain let bindings with same name.
uint64_t NameClashScopeLeak::branch_let_clash(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return (a0 * UINT64_C(2));
  }
}

/// Three consecutive matches, each with same binding variable name pattern.
uint64_t NameClashScopeLeak::triple_head(const List<uint64_t> &l1,
                                         const List<uint64_t> &l2,
                                         const List<uint64_t> &l3) {
  uint64_t a = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
      return a0;
    }
  }();
  uint64_t b = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(l2.v());
      return a00;
    }
  }();
  uint64_t c = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l3.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a01, a11] = std::get<typename List<uint64_t>::Cons>(l3.v());
      return a01;
    }
  }();
  return ((a + b) + c);
}

/// Matching on a pair where both components are lists.
uint64_t NameClashScopeLeak::pair_match(
    const std::pair<List<uint64_t>, List<uint64_t>> &p) {
  const auto &[l1, l2] = p;
  uint64_t h1 = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
      return a0;
    }
  }();
  uint64_t h2 = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(l2.v());
      return a00;
    }
  }();
  return (h1 + h2);
}
