#include "match_ref_after_move.h"

MatchRefAfterMove::mypair<uint64_t, uint64_t>
MatchRefAfterMove::head_and_tail_length(
    const MatchRefAfterMove::mylist<uint64_t> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(l.v())) {
    return mypair<uint64_t, uint64_t>::mkpair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1] =
        std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(l.v());
    return mypair<uint64_t, uint64_t>::mkpair(a0, (*a1).mylist_length());
  }
}

/// Pattern 2: Nested match where inner match is on a field of outer.
/// After inner match, outer pattern variables are still used.
///
/// BUG HYPOTHESIS: Outer match creates structured bindings into the
/// outer value. Inner match on the tail might consume/move the tail.
/// If the outer head h is a reference into the outer value, and
/// the outer value is freed because the inner match consumes the
/// tail (sole remaining reference), h dangles.
uint64_t MatchRefAfterMove::nested_match_probe(
    const MatchRefAfterMove::mylist<uint64_t> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(l.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(_sv0.v())) {
      return a0;
    } else {
      const auto &[a00, a10] =
          std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(
              _sv0.v());
      return ((a0 + a00) + (*a10).mylist_length());
    }
  }
}

/// Pattern 3: Build a pair where one element is from a match
/// and the other is a function of the matched value.
/// Tests evaluation order in pair construction.
MatchRefAfterMove::mypair<uint64_t, MatchRefAfterMove::mylist<uint64_t>>
MatchRefAfterMove::match_into_pair(
    const MatchRefAfterMove::mylist<uint64_t> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(l.v())) {
    return mypair<uint64_t, MatchRefAfterMove::mylist<uint64_t>>::mkpair(
        UINT64_C(0), mylist<uint64_t>::mynil());
  } else {
    const auto &[a0, a1] =
        std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(l.v());
    return mypair<uint64_t, MatchRefAfterMove::mylist<uint64_t>>::mkpair(
        a0, mylist<uint64_t>::mycons((a0 + UINT64_C(1)), *a1));
  }
}

/// Pattern 4: Double match on same value.
/// First match extracts head, second match extracts tail.
/// Between matches, the value might be moved.
MatchRefAfterMove::mypair<uint64_t, MatchRefAfterMove::mylist<uint64_t>>
MatchRefAfterMove::double_match(const MatchRefAfterMove::mylist<uint64_t> &l) {
  uint64_t h = [&]() {
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(l.v());
      return a0;
    }
  }();
  MatchRefAfterMove::mylist<uint64_t> t = [&]() {
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(l.v())) {
      return mylist<uint64_t>::mynil();
    } else {
      const auto &[a00, a10] =
          std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(l.v());
      return *a10;
    }
  }();
  return mypair<uint64_t, MatchRefAfterMove::mylist<uint64_t>>::mkpair(
      h, std::move(t));
}

uint64_t
MatchRefAfterMove::mylist_sum(const MatchRefAfterMove::mylist<uint64_t> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(l.v());
    return (a0 + mylist_sum(*a1));
  }
}

uint64_t MatchRefAfterMove::complex_match(
    const MatchRefAfterMove::either<MatchRefAfterMove::mylist<uint64_t>,
                                    MatchRefAfterMove::mylist<uint64_t>> &e) {
  if (std::holds_alternative<typename MatchRefAfterMove::either<
          MatchRefAfterMove::mylist<uint64_t>,
          MatchRefAfterMove::mylist<uint64_t>>::Left>(e.v())) {
    const auto &[a0] = std::get<typename MatchRefAfterMove::either<
        MatchRefAfterMove::mylist<uint64_t>,
        MatchRefAfterMove::mylist<uint64_t>>::Left>(e.v());
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(a0.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a00, a10] =
          std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(
              a0.v());
      return a00;
    }
  } else {
    const auto &[a0] = std::get<typename MatchRefAfterMove::either<
        MatchRefAfterMove::mylist<uint64_t>,
        MatchRefAfterMove::mylist<uint64_t>>::Right>(e.v());
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<uint64_t>::Mynil>(a0.v())) {
      return UINT64_C(999);
    } else {
      const auto &[a00, a10] =
          std::get<typename MatchRefAfterMove::mylist<uint64_t>::Mycons>(
              a0.v());
      return (a00 + (*a10).mylist_length());
    }
  }
}
