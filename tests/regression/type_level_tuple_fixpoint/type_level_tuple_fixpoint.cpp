#include "type_level_tuple_fixpoint.h"

Nat TypeLevelTupleFixpoint::fst3(TypeLevelTupleFixpoint::tup t) {
  return crane::any_cast<Nat>(
      crane::any_cast<std::pair<crane::obj, crane::obj>>(std::move(t)).first);
}
