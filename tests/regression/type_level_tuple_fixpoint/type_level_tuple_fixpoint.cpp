#include "type_level_tuple_fixpoint.h"

Nat TypeLevelTupleFixpoint::fst3(TypeLevelTupleFixpoint::tup t) {
  return std::any_cast<std::pair<Nat, std::any>>(t).first;
}
