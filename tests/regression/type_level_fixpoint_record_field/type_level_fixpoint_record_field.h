#ifndef INCLUDED_TYPE_LEVEL_FIXPOINT_RECORD_FIELD
#define INCLUDED_TYPE_LEVEL_FIXPOINT_RECORD_FIELD

#include "crane_fn.h"
#include <any>
#include <utility>

/// A record field whose type is a `Type`-valued `Fixpoint` applied to a
/// literal (`ty 2`, i.e. a nested pair) is erased, so projecting it must not
/// inherit the enclosing definition's return type as a cast target.
struct TypeLevelFixpointRecordField {
  using ty = std::any;

  struct holder {
    uint64_t lvl;
    ty val;
  };

  static inline const uint64_t go =
      crane_any_cast<std::pair<uint64_t, uint64_t>>(
          crane_any_cast<std::pair<std::pair<uint64_t, uint64_t>,
                                   std::pair<uint64_t, uint64_t>>>(
              std::make_pair(std::any(std::make_pair(std::any(UINT64_C(1)),
                                                     std::any(UINT64_C(2)))),
                             std::any(std::make_pair(std::any(UINT64_C(3)),
                                                     std::any(UINT64_C(4))))))
              .first)
          .first;
};

#endif // INCLUDED_TYPE_LEVEL_FIXPOINT_RECORD_FIELD
