#include <reuse_alias.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Increment the head — candidate for reuse optimization when use_count = 1.
std::shared_ptr<ReuseAlias::mylist<unsigned int>> ReuseAlias::inc_head(
    const std::shared_ptr<ReuseAlias::mylist<unsigned int>> &l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<unsigned int>::Mynil>(
          l->v())) {
    return mylist<unsigned int>::mynil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseAlias::mylist<unsigned int>::Mycons>(l->v());
    return mylist<unsigned int>::mycons((d_a0 + 1u), d_a1);
  }
}

/// Use the same list twice: once through inc_head, once directly.
/// If reuse fires on the first call (because evaluation order is
/// unspecified), the second use of l sees the already-mutated list.
__attribute__((pure))
std::pair<std::shared_ptr<ReuseAlias::mylist<unsigned int>>,
          std::shared_ptr<ReuseAlias::mylist<unsigned int>>>
ReuseAlias::double_use(std::shared_ptr<ReuseAlias::mylist<unsigned int>> l) {
  return std::make_pair(inc_head(l), l);
}

/// Pass the same list to two different functions.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
ReuseAlias::double_call(
    const std::shared_ptr<ReuseAlias::mylist<unsigned int>> &l) {
  return std::make_pair(length<unsigned int>(l),
                        length<unsigned int>(inc_head(l)));
}

/// Alias through let-binding, then use both the alias and the original
/// in a match.
__attribute__((pure))
std::pair<std::shared_ptr<ReuseAlias::mylist<unsigned int>>, unsigned int>
ReuseAlias::alias_and_match(
    std::shared_ptr<ReuseAlias::mylist<unsigned int>> l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<unsigned int>::Mynil>(
          l->v())) {
    return std::make_pair(std::move(l), 0u);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseAlias::mylist<unsigned int>::Mycons>(l->v());
    return std::make_pair(std::move(l), d_a0);
  }
}

/// Build a result that refers to the scrutinee AND a pattern variable
/// from the same match.
__attribute__((pure))
std::pair<std::shared_ptr<ReuseAlias::mylist<unsigned int>>,
          std::shared_ptr<ReuseAlias::mylist<unsigned int>>>
ReuseAlias::scrutinee_in_branch(
    std::shared_ptr<ReuseAlias::mylist<unsigned int>> l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<unsigned int>::Mynil>(
          l->v())) {
    return std::make_pair(mylist<unsigned int>::mynil(),
                          mylist<unsigned int>::mynil());
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseAlias::mylist<unsigned int>::Mycons>(l->v());
    return std::make_pair(std::move(l), d_a1);
  }
}

/// Chain inc_head: each call might try to reuse.
std::shared_ptr<ReuseAlias::mylist<unsigned int>> ReuseAlias::triple_inc(
    const std::shared_ptr<ReuseAlias::mylist<unsigned int>> &l) {
  return inc_head(inc_head(inc_head(l)));
}
