#include <name_clash_let_match.h>

#include <type_traits>
#include <utility>
#include <variant>

/// Variable name 'a' used in both let and match binding.
__attribute__((pure)) unsigned int
NameClashLetMatch::let_shadows_match(const NameClashLetMatch::either &e) {
  unsigned int a = 100u;
  if (std::holds_alternative<typename NameClashLetMatch::either::Left>(e.v())) {
    const auto &[d_a0] =
        std::get<typename NameClashLetMatch::either::Left>(e.v());
    return d_a0;
  } else {
    const auto &[d_a0] =
        std::get<typename NameClashLetMatch::either::Right>(e.v());
    return (d_a0 + a);
  }
}

/// Match where the same variable name is used in multiple branches
__attribute__((pure)) unsigned int
NameClashLetMatch::same_name_branches(const NameClashLetMatch::either &e,
                                      const NameClashLetMatch::triple &t) {
  if (std::holds_alternative<typename NameClashLetMatch::either::Left>(e.v())) {
    const auto &[d_a0] =
        std::get<typename NameClashLetMatch::either::Left>(e.v());
    const auto &[d_a00, d_a10, d_a20] =
        std::get<typename NameClashLetMatch::triple::MkTriple>(t.v());
    return (((d_a0 + d_a00) + d_a10) + d_a20);
  } else {
    const auto &[d_a0] =
        std::get<typename NameClashLetMatch::either::Right>(e.v());
    const auto &[d_a00, d_a10, d_a20] =
        std::get<typename NameClashLetMatch::triple::MkTriple>(t.v());
    return (((d_a0 * d_a00) * d_a10) * d_a20);
  }
}
