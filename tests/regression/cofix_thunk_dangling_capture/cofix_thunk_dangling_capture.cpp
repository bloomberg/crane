#include "cofix_thunk_dangling_capture.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Memory safety: use after return.  A corecursive branch builds a local
/// fixpoint lambda go that captures m (a local of h) by reference, then
/// returns stream::lazy_([=] { return go(...); }).  The thunk copies go
/// but not what it refers to; when it is forced after h returned, m is a
/// dead stack slot, so h(m) recurses on garbage (the test runs away in time
/// and memory).  CRANE_CHECK_IR=1 reported it first: "closure captures: the
/// local fixpoint lambda go reads its scope by reference and escapes it".
/// Escape analysis now counts what the value of a body suspended whole names,
/// and what a suspended constructor's arguments name, as escaping, so go
/// holds copies.
CofixThunkDanglingCapture::stream
CofixThunkDanglingCapture::sconst(uint64_t n) {
  return stream::lazy_(
      [=]() -> typename CofixThunkDanglingCapture::stream::SCons {
        return {n, sconst(n)};
      });
}

CofixThunkDanglingCapture::stream CofixThunkDanglingCapture::h(uint64_t n) {
  if (n <= 0) {
    return stream::lazy_([]() -> CofixThunkDanglingCapture::stream {
      return sconst(UINT64_C(0));
    });
  } else {
    uint64_t m = n - 1;
    auto go =
        [=](List<uint64_t> l,
            CofixThunkDanglingCapture::stream)
             -> CofixThunkDanglingCapture::stream {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          List<uint64_t> _loop_l = std::move(l);
          while (true) {
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _loop_l.v_mut())) {
              return h(m);
            } else {
              auto &[_, a1] =
                  std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
              const List<uint64_t> &a1_value = *a1;
              _loop_l = List<uint64_t>(a1_value);
            }
          }
        };
    return stream::lazy_([=]() -> CofixThunkDanglingCapture::stream {
      return go(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
                [&]() -> CofixThunkDanglingCapture::stream {
                  if (n <= 0) {
                    return h(m);
                  } else {
                    uint64_t _x = n - 1;
                    return sconst(UINT64_C(2));
                  }
                }());
    });
  }
}

/// Nested local fixpoints, the inner returning the outer's accumulator.
CofixThunkDanglingCapture::stream
CofixThunkDanglingCapture::g2(const CofixThunkDanglingCapture::tree &t0) {
  if (std::holds_alternative<typename CofixThunkDanglingCapture::tree::Leaf>(
          t0.v())) {
    return stream::lazy_([]() -> CofixThunkDanglingCapture::stream {
      return sconst(UINT64_C(0));
    });
  } else {
    const auto &[a0, _, _] =
        std::get<typename CofixThunkDanglingCapture::tree::Node>(t0.v());
    const CofixThunkDanglingCapture::tree &a0_value = *a0;
    List<uint64_t> l = List<uint64_t>::nil();
    CofixThunkDanglingCapture::stream acc9 = sconst(UINT64_C(0));
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return stream::lazy_(
          [=]() -> CofixThunkDanglingCapture::stream { return g2(a0_value); });
    } else {
      auto go12 =
          [=](List<std::optional<uint64_t>> l2,
              CofixThunkDanglingCapture::stream)
               -> CofixThunkDanglingCapture::stream {
            // Loop replaces the tail recursion: each recursive call updates the
            // loop variables.
            List<std::optional<uint64_t>> _loop_l2 = std::move(l2);
            while (true) {
              if (std::holds_alternative<
                      typename List<std::optional<uint64_t>>::Nil>(
                      _loop_l2.v_mut())) {
                return acc9;
              } else {
                auto &[_, a11] =
                    std::get<typename List<std::optional<uint64_t>>::Cons>(
                        _loop_l2.v_mut());
                const List<std::optional<uint64_t>> &a11_value = *a11;
                _loop_l2 = List<std::optional<uint64_t>>(a11_value);
              }
            }
          };
      return stream::lazy_([=]() -> CofixThunkDanglingCapture::stream {
        return go12(List<std::optional<uint64_t>>::nil(), sconst(UINT64_C(0)));
      });
    }
  }
}

List<uint64_t>
CofixThunkDanglingCapture::stake(uint64_t k,
                                 const CofixThunkDanglingCapture::stream &s) {
  if (k <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t k_ = k - 1;
    const auto &[a0, a1] =
        std::get<typename CofixThunkDanglingCapture::stream::SCons>(s.v());
    return List<uint64_t>::cons(a0, stake(k_, a1));
  }
}
