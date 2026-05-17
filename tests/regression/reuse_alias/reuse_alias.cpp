#include "reuse_alias.h"

/// Increment the head — candidate for reuse optimization when use_count = 1.
ReuseAlias::mylist<uint64_t>
ReuseAlias::inc_head(const ReuseAlias::mylist<uint64_t> &l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<uint64_t>::Mynil>(
          l.v())) {
    return mylist<uint64_t>::mynil();
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseAlias::mylist<uint64_t>::Mycons>(l.v());
    return mylist<uint64_t>::mycons((a0 + UINT64_C(1)), *a1);
  }
}

/// Use the same list twice: once through inc_head, once directly.
/// If reuse fires on the first call (because evaluation order is
/// unspecified), the second use of l sees the already-mutated list.
std::pair<ReuseAlias::mylist<uint64_t>, ReuseAlias::mylist<uint64_t>>
ReuseAlias::double_use(ReuseAlias::mylist<uint64_t> l) {
  return std::make_pair(inc_head(l), l);
}

/// Pass the same list to two different functions.
std::pair<uint64_t, uint64_t>
ReuseAlias::double_call(const ReuseAlias::mylist<uint64_t> &l) {
  return std::make_pair(length<uint64_t>(l), length<uint64_t>(inc_head(l)));
}

/// Alias through let-binding, then use both the alias and the original
/// in a match.
std::pair<ReuseAlias::mylist<uint64_t>, uint64_t>
ReuseAlias::alias_and_match(ReuseAlias::mylist<uint64_t> l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<uint64_t>::Mynil>(
          l.v_mut())) {
    return std::make_pair(std::move(l), UINT64_C(0));
  } else {
    auto &[a0, a1] =
        std::get<typename ReuseAlias::mylist<uint64_t>::Mycons>(l.v_mut());
    return std::make_pair(std::move(l), std::move(a0));
  }
}

/// Build a result that refers to the scrutinee AND a pattern variable
/// from the same match.
std::pair<ReuseAlias::mylist<uint64_t>, ReuseAlias::mylist<uint64_t>>
ReuseAlias::scrutinee_in_branch(ReuseAlias::mylist<uint64_t> l) {
  if (std::holds_alternative<typename ReuseAlias::mylist<uint64_t>::Mynil>(
          l.v_mut())) {
    return std::make_pair(mylist<uint64_t>::mynil(), mylist<uint64_t>::mynil());
  } else {
    auto &[a0, a1] =
        std::get<typename ReuseAlias::mylist<uint64_t>::Mycons>(l.v_mut());
    return std::make_pair(std::move(l), *a1);
  }
}

/// Chain inc_head: each call might try to reuse.
ReuseAlias::mylist<uint64_t>
ReuseAlias::triple_inc(const ReuseAlias::mylist<uint64_t> &l) {
  return inc_head(inc_head(inc_head(l)));
}
