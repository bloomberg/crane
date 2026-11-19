#include "stream_match_v_mut_missing.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A local fixpoint over a list of streams, called on a literal [], matches
/// an element with SCons h _: the inlined match takes the element by
/// mutable reference, a0.v_mut(), which a coinductive type does not have
/// ("no member named 'v_mut' in 'stream'").
std::pair<uint64_t, uint64_t> StreamMatchVMutMissing::g(uint64_t n) {
  List<StreamMatchVMutMissing::stream> l =
      List<StreamMatchVMutMissing::stream>::nil();
  if (std::holds_alternative<typename List<StreamMatchVMutMissing::stream>::Nil>(
          l.v_mut())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    auto &[a0, _] = std::get<
        typename List<StreamMatchVMutMissing::stream>::Cons>(l.v_mut());
    auto &[a00, _] =
        std::get<typename StreamMatchVMutMissing::stream::SCons>(a0.v_mut());
    return std::make_pair(n, std::move(a00));
  }
}
