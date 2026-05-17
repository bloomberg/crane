#include "match_ref_after_move.h"

MatchRefAfterMove::mypair<unsigned int, unsigned int>
MatchRefAfterMove::head_and_tail_length(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
    return mypair<unsigned int, unsigned int>::mkpair(0u, 0u);
  } else {
    const auto &[a0, a1] =
        std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
            l.v());
    return mypair<unsigned int, unsigned int>::mkpair(a0,
                                                      (*a1).mylist_length());
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
unsigned int MatchRefAfterMove::nested_match_probe(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
            l.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(
            _sv0.v())) {
      return a0;
    } else {
      const auto &[a00, a10] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              _sv0.v());
      return ((a0 + a00) + (*a10).mylist_length());
    }
  }
}

/// Pattern 3: Build a pair where one element is from a match
/// and the other is a function of the matched value.
/// Tests evaluation order in pair construction.
MatchRefAfterMove::mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>
MatchRefAfterMove::match_into_pair(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
    return mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>::
        mkpair(0u, mylist<unsigned int>::mynil());
  } else {
    const auto &[a0, a1] =
        std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
            l.v());
    return mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>::
        mkpair(a0, mylist<unsigned int>::mycons((a0 + 1u), *a1));
  }
}

/// Pattern 4: Double match on same value.
/// First match extracts head, second match extracts tail.
/// Between matches, the value might be moved.
MatchRefAfterMove::mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>
MatchRefAfterMove::double_match(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  unsigned int h = [&]() {
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              l.v());
      return a0;
    }
  }();
  MatchRefAfterMove::mylist<unsigned int> t = [&]() {
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
      return mylist<unsigned int>::mynil();
    } else {
      const auto &[a00, a10] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              l.v());
      return *a10;
    }
  }();
  return mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>::mkpair(
      h, std::move(t));
}

unsigned int MatchRefAfterMove::mylist_sum(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
            l.v());
    return (a0 + mylist_sum(*a1));
  }
}

unsigned int MatchRefAfterMove::complex_match(
    const MatchRefAfterMove::either<MatchRefAfterMove::mylist<unsigned int>,
                                    MatchRefAfterMove::mylist<unsigned int>>
        &e) {
  if (std::holds_alternative<typename MatchRefAfterMove::either<
          MatchRefAfterMove::mylist<unsigned int>,
          MatchRefAfterMove::mylist<unsigned int>>::Left>(e.v())) {
    const auto &[a0] = std::get<typename MatchRefAfterMove::either<
        MatchRefAfterMove::mylist<unsigned int>,
        MatchRefAfterMove::mylist<unsigned int>>::Left>(e.v());
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(a0.v())) {
      return 0u;
    } else {
      const auto &[a00, a10] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              a0.v());
      return a00;
    }
  } else {
    const auto &[a0] = std::get<typename MatchRefAfterMove::either<
        MatchRefAfterMove::mylist<unsigned int>,
        MatchRefAfterMove::mylist<unsigned int>>::Right>(e.v());
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(a0.v())) {
      return 999u;
    } else {
      const auto &[a00, a10] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              a0.v());
      return (a00 + (*a10).mylist_length());
    }
  }
}
