#include "type_level_tuple_fixpoint.h"

Nat TypeLevelTupleFixpoint::fst3(TypeLevelTupleFixpoint::tup t) {
  return std::any_cast<Nat>(
      std::any_cast<std::pair<std::any, std::any>>(t).first);
}
