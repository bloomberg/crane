#include "name_clash_match_match.h"

NameClashMatchMatch::tree
NameClashMatchMatch::choose_subtree(NameClashMatchMatch::Dir d,
                                    const NameClashMatchMatch::tree &t) {
  if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(t.v())) {
    return tree::leaf();
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NameClashMatchMatch::tree::Node>(t.v());
    switch (d) {
    case Dir::GOLEFT: {
      return *a0;
    }
    case Dir::GORIGHT: {
      return *a2;
    }
    default:
      std::unreachable();
    }
  }
}

/// Match on the result of choose_subtree (which itself contains a match).
uint64_t
NameClashMatchMatch::subtree_value(NameClashMatchMatch::Dir d,
                                   const NameClashMatchMatch::tree &t) {
  auto &&_sv = choose_subtree(d, t);
  if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
          _sv.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NameClashMatchMatch::tree::Node>(_sv.v());
    return a1;
  }
}

/// Inline match-on-match: both matches are expressions.
uint64_t
NameClashMatchMatch::inline_match_match(NameClashMatchMatch::Dir d,
                                        const NameClashMatchMatch::tree &t) {
  auto &&_sv = [&]() {
    switch (d) {
    case Dir::GOLEFT: {
      return t;
    }
    case Dir::GORIGHT: {
      return tree::leaf();
    }
    default:
      std::unreachable();
    }
  }();
  if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
          _sv.v())) {
    return UINT64_C(100);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NameClashMatchMatch::tree::Node>(_sv.v());
    return a1;
  }
}

/// Two matches on the same scrutinee.
uint64_t NameClashMatchMatch::double_match(const NameClashMatchMatch::tree &t) {
  uint64_t a = [&]() {
    if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
            t.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename NameClashMatchMatch::tree::Node>(t.v());
      return a1;
    }
  }();
  uint64_t b = [&]() {
    if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
            t.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename NameClashMatchMatch::tree::Node>(t.v());
      auto &&_sv1 = *a00;
      if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
              _sv1.v())) {
        return UINT64_C(2);
      } else {
        const auto &[a01, a11, a21] =
            std::get<typename NameClashMatchMatch::tree::Node>(_sv1.v());
        return a11;
      }
    }
  }();
  return (a + b);
}

/// Match where the scrutinee is a function call that returns an inductive,
/// and the result is used in another match.
uint64_t NameClashMatchMatch::chained(const NameClashMatchMatch::tree &t) {
  if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(t.v())) {
    return UINT64_C(42);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NameClashMatchMatch::tree::Node>(t.v());
    return a1;
  }
}
