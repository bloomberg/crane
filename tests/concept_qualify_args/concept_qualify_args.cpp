#include "concept_qualify_args.h"

uint64_t ConceptQualifyArgs::NatElems::head_or(uint64_t d) {
  auto &&_sv = elements;
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return d;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    return a0;
  }
}
