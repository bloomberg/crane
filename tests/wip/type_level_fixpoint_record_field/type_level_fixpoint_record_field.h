#ifndef INCLUDED_TYPE_LEVEL_FIXPOINT_RECORD_FIELD
#define INCLUDED_TYPE_LEVEL_FIXPOINT_RECORD_FIELD

#include <any>
#include <utility>

/// WIP: A record field whose type is a `Type`-valued `Fixpoint` applied to a
/// literal
/// (`ty 2`, i.e. a nested pair) is emitted as `uint64_t`, so the projections
/// on it do not type-check.
struct TypeLevelFixpointRecordField {
  using ty = std::any;

  struct holder {
    uint64_t lvl;
    ty val;
  };

  static inline const uint64_t go =
      ([]() {
        auto val0 = std::make_pair(std::make_pair(UINT64_C(1), UINT64_C(2)),
                                   std::make_pair(UINT64_C(3), UINT64_C(4)));
        return std::any_cast<uint64_t>(val0);
      }()
           .first)
          .first;
};

#endif // INCLUDED_TYPE_LEVEL_FIXPOINT_RECORD_FIELD
