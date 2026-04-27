#include <match_ref_after_move.h>

__attribute__((pure)) MatchRefAfterMove::mypair<unsigned int, unsigned int>
MatchRefAfterMove::head_and_tail_length(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
    return mypair<unsigned int, unsigned int>::mkpair(0u, 0u);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
            l.v());
    return mypair<unsigned int, unsigned int>::mkpair(
        d_a0, (*(d_a1)).mylist_length());
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
__attribute__((pure)) unsigned int MatchRefAfterMove::nested_match_probe(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
            l.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(
            _sv0.v())) {
      return d_a0;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              _sv0.v());
      return ((d_a0 + d_a00) + (*(d_a10)).mylist_length());
    }
  }
}

/// Pattern 3: Build a pair where one element is from a match
/// and the other is a function of the matched value.
/// Tests evaluation order in pair construction.
__attribute__((pure))
MatchRefAfterMove::mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>
MatchRefAfterMove::match_into_pair(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
    return mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>::
        mkpair(0u, mylist<unsigned int>::mynil());
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
            l.v());
    return mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>::
        mkpair(d_a0, mylist<unsigned int>::mycons((d_a0 + 1u), *(d_a1)));
  }
}

/// Pattern 4: Double match on same value.
/// First match extracts head, second match extracts tail.
/// Between matches, the value might be moved.
__attribute__((pure))
MatchRefAfterMove::mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>
MatchRefAfterMove::double_match(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  unsigned int h = [&]() {
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              l.v());
      return d_a0;
    }
  }();
  MatchRefAfterMove::mylist<unsigned int> t = [&]() {
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
      return mylist<unsigned int>::mynil();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              l.v());
      return *(d_a10);
    }
  }();
  return mypair<unsigned int, MatchRefAfterMove::mylist<unsigned int>>::mkpair(
      h, t);
}

__attribute__((pure)) unsigned int MatchRefAfterMove::mylist_sum(
    const MatchRefAfterMove::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
            l.v());
    return (d_a0 + mylist_sum(*(d_a1)));
  }
}

__attribute__((pure)) unsigned int MatchRefAfterMove::complex_match(
    const MatchRefAfterMove::either<MatchRefAfterMove::mylist<unsigned int>,
                                    MatchRefAfterMove::mylist<unsigned int>>
        &e) {
  if (std::holds_alternative<typename MatchRefAfterMove::either<
          MatchRefAfterMove::mylist<unsigned int>,
          MatchRefAfterMove::mylist<unsigned int>>::Left>(e.v())) {
    const auto &[d_a0] = std::get<typename MatchRefAfterMove::either<
        MatchRefAfterMove::mylist<unsigned int>,
        MatchRefAfterMove::mylist<unsigned int>>::Left>(e.v());
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(
            d_a0.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              d_a0.v());
      return d_a00;
    }
  } else {
    const auto &[d_a0] = std::get<typename MatchRefAfterMove::either<
        MatchRefAfterMove::mylist<unsigned int>,
        MatchRefAfterMove::mylist<unsigned int>>::Right>(e.v());
    if (std::holds_alternative<
            typename MatchRefAfterMove::mylist<unsigned int>::Mynil>(
            d_a0.v())) {
      return 999u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename MatchRefAfterMove::mylist<unsigned int>::Mycons>(
              d_a0.v());
      return (d_a00 + (*(d_a10)).mylist_length());
    }
  }
}
