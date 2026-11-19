#include "absurd_proof_only_definition.h"

uint64_t AbsurdProofOnlyDefinition::absurd_nat() {
  throw std::logic_error("absurd case");
}

List<uint64_t> AbsurdProofOnlyDefinition::absurd_list() {
  throw std::logic_error("absurd case");
}
