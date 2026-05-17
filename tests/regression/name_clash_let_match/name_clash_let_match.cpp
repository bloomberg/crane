#include "name_clash_let_match.h"

/// Variable name 'a' used in both let and match binding.
unsigned int
NameClashLetMatch::let_shadows_match(const NameClashLetMatch::either &e) {
  unsigned int a = 100u;
  if (std::holds_alternative<typename NameClashLetMatch::either::Left>(e.v())) {
    const auto &[a1] =
        std::get<typename NameClashLetMatch::either::Left>(e.v());
    return a1;
  } else {
    const auto &[a0] =
        std::get<typename NameClashLetMatch::either::Right>(e.v());
    return (a0 + a);
  }
}

/// Match where the same variable name is used in multiple branches
unsigned int
NameClashLetMatch::same_name_branches(const NameClashLetMatch::either &e,
                                      const NameClashLetMatch::triple &t) {
  if (std::holds_alternative<typename NameClashLetMatch::either::Left>(e.v())) {
    const auto &[a0] =
        std::get<typename NameClashLetMatch::either::Left>(e.v());
    const auto &[a00, a10, a20] =
        std::get<typename NameClashLetMatch::triple::MkTriple>(t.v());
    return (((a0 + a00) + a10) + a20);
  } else {
    const auto &[a0] =
        std::get<typename NameClashLetMatch::either::Right>(e.v());
    const auto &[a00, a10, a20] =
        std::get<typename NameClashLetMatch::triple::MkTriple>(t.v());
    return (((a0 * a00) * a10) * a20);
  }
}
