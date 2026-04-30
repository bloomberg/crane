#include <reuse_alias.h>

/// Increment the head — candidate for reuse optimization when use_count = 1.
ReuseAlias::mylist<unsigned int>
ReuseAlias::inc_head(const ReuseAlias::mylist<unsigned int> &l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<unsigned int>::Mynil>(
          l.v())) {
    return mylist<unsigned int>::mynil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseAlias::mylist<unsigned int>::Mycons>(l.v());
    return mylist<unsigned int>::mycons((d_a0 + 1u), *(d_a1));
  }
}

/// Use the same list twice: once through inc_head, once directly.
/// If reuse fires on the first call (because evaluation order is
/// unspecified), the second use of l sees the already-mutated list.
std::pair<ReuseAlias::mylist<unsigned int>, ReuseAlias::mylist<unsigned int>>
ReuseAlias::double_use(ReuseAlias::mylist<unsigned int> l) {
  return std::make_pair(inc_head(l), l);
}

/// Pass the same list to two different functions.
std::pair<unsigned int, unsigned int>
ReuseAlias::double_call(const ReuseAlias::mylist<unsigned int> &l) {
  return std::make_pair(length<unsigned int>(l),
                        length<unsigned int>(inc_head(l)));
}

/// Alias through let-binding, then use both the alias and the original
/// in a match.
std::pair<ReuseAlias::mylist<unsigned int>, unsigned int>
ReuseAlias::alias_and_match(ReuseAlias::mylist<unsigned int> l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<unsigned int>::Mynil>(
          l.v_mut())) {
    return std::make_pair(l, 0u);
  } else {
    auto &[d_a0, d_a1] =
        std::get<typename ReuseAlias::mylist<unsigned int>::Mycons>(l.v_mut());
    return std::make_pair(l, d_a0);
  }
}

/// Build a result that refers to the scrutinee AND a pattern variable
/// from the same match.
std::pair<ReuseAlias::mylist<unsigned int>, ReuseAlias::mylist<unsigned int>>
ReuseAlias::scrutinee_in_branch(ReuseAlias::mylist<unsigned int> l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<unsigned int>::Mynil>(
          l.v_mut())) {
    return std::make_pair(mylist<unsigned int>::mynil(),
                          mylist<unsigned int>::mynil());
  } else {
    auto &[d_a0, d_a1] =
        std::get<typename ReuseAlias::mylist<unsigned int>::Mycons>(l.v_mut());
    return std::make_pair(l, *(d_a1));
  }
}

/// Chain inc_head: each call might try to reuse.
ReuseAlias::mylist<unsigned int>
ReuseAlias::triple_inc(const ReuseAlias::mylist<unsigned int> &l) {
  return inc_head(inc_head(inc_head(l)));
}
