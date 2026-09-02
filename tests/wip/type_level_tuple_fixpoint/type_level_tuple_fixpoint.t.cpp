#include <type_level_tuple_fixpoint.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::S>(TypeLevelTupleFixpoint::run.v()));
  return 0;
}
