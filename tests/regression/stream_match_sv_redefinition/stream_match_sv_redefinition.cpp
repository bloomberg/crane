#include "stream_match_sv_redefinition.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Matching a stream literal, then a list built from its head, then the head
/// itself: the nested matches each declare auto &&_sv in one scope
/// ("redefinition of '_sv'"), and an alternative test names a type outside
/// the variant ("type not found in type list").
StreamMatchSvRedefinition::stream
StreamMatchSvRedefinition::sconst(uint64_t n) {
  return stream::lazy_(
      [=]() mutable -> typename StreamMatchSvRedefinition::stream::SCons {
        return {n, sconst(n)};
      });
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
