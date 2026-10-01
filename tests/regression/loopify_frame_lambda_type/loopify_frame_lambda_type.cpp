#include "loopify_frame_lambda_type.h"

/// comb recurses in the first argument of bind, so Set Crane Loopify
/// gives it a frame stack whose resume frame saves the continuation.  The
/// frame declares that field's type as
/// std::decay_t<decltype([](std::pair<...> x0) { ... })> -- the type of a
/// lambda *expression* written inside the struct -- and a lambda expression
/// has a type of its own: the continuation built at the push site is a
/// different closure type, so the push does not compile ("no viable
/// conversion from '(lambda at ...)'").  The body copied into the
/// decltype also stands the captured pattern variables in with
/// std::declval<T1 &>(), which trips libc++'s "std::declval can only be
/// used in an unevaluated context" static assertion, since a lambda body is
/// evaluated.
///
/// Found in Vellvm with the global Set Crane Loopify:
/// Denotation.combine_lists_varargs, 3 of its 59 errors.
bool LoopifyFrameLambdaType::check(std::monostate) {
  auto &&_sv = comb<uint64_t, uint64_t>(
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(20),
              List<uint64_t>::cons(
                  UINT64_C(30),
                  List<uint64_t>::cons(UINT64_C(40), List<uint64_t>::nil())))));
  if (std::holds_alternative<typename LoopifyFrameLambdaType::res<
          std::pair<List<std::pair<uint64_t, uint64_t>>, List<uint64_t>>>::Err>(
          _sv.v())) {
    return false;
  } else {
    const auto &[x0] = std::get<typename LoopifyFrameLambdaType::res<
        std::pair<List<std::pair<uint64_t, uint64_t>>, List<uint64_t>>>::Ok>(
        _sv.v());
    const auto &[pairs, rest] = x0;
    return (
        pairs.length() == UINT64_C(2) &&
        rest.template fold_left<uint64_t>(
            [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
            UINT64_C(0)) == UINT64_C(70));
  }
}
