#include <name_clash_match_match.h>

__attribute__((pure)) NameClashMatchMatch::tree
NameClashMatchMatch::choose_subtree(const NameClashMatchMatch::Dir d,
                                    const NameClashMatchMatch::tree &t) {
  if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(t.v())) {
    return tree::leaf();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NameClashMatchMatch::tree::Node>(t.v());
    switch (d) {
    case Dir::e_GOLEFT: {
      return *(d_a0);
    }
    case Dir::e_GORIGHT: {
      return *(d_a2);
    }
    default:
      std::unreachable();
    }
  }
}

/// Match on the result of choose_subtree (which itself contains a match).
__attribute__((pure)) unsigned int
NameClashMatchMatch::subtree_value(const NameClashMatchMatch::Dir d,
                                   const NameClashMatchMatch::tree &t) {
  auto &&_sv = choose_subtree(d, t);
  if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
          _sv.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NameClashMatchMatch::tree::Node>(_sv.v());
    return d_a1;
  }
}

/// Inline match-on-match: both matches are expressions.
__attribute__((pure)) unsigned int
NameClashMatchMatch::inline_match_match(const NameClashMatchMatch::Dir d,
                                        const NameClashMatchMatch::tree &t) {
  auto &&_sv = [&]() {
    switch (d) {
    case Dir::e_GOLEFT: {
      return t;
    }
    case Dir::e_GORIGHT: {
      return tree::leaf();
    }
    default:
      std::unreachable();
    }
  }();
  if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
          _sv.v())) {
    return 100u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NameClashMatchMatch::tree::Node>(_sv.v());
    return d_a1;
  }
}

/// Two matches on the same scrutinee.
__attribute__((pure)) unsigned int
NameClashMatchMatch::double_match(const NameClashMatchMatch::tree &t) {
  unsigned int a = [&]() {
    if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
            t.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename NameClashMatchMatch::tree::Node>(t.v());
      return d_a1;
    }
  }();
  unsigned int b = [&]() {
    if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
            t.v())) {
      return 1u;
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename NameClashMatchMatch::tree::Node>(t.v());
      auto &&_sv1 = *(d_a00);
      if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(
              _sv1.v())) {
        return 2u;
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename NameClashMatchMatch::tree::Node>(_sv1.v());
        return d_a11;
      }
    }
  }();
  return (a + b);
}

/// Match where the scrutinee is a function call that returns an inductive,
/// and the result is used in another match.
__attribute__((pure)) unsigned int
NameClashMatchMatch::chained(const NameClashMatchMatch::tree &t) {
  if (std::holds_alternative<typename NameClashMatchMatch::tree::Leaf>(t.v())) {
    return 42u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NameClashMatchMatch::tree::Node>(t.v());
    return d_a1;
  }
}
