#include "type_level_tuple_fixpoint.h"

Nat TypeLevelTupleFixpoint::fst3(TypeLevelTupleFixpoint::tup t) {
  return crane_any_cast<
             std::pair<Nat, std::pair<Nat, std::pair<Nat, std::monostate>>>>(t)
      .first;
}
