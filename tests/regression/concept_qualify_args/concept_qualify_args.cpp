#include "concept_qualify_args.h"

unsigned int ConceptQualifyArgs::NatElems::head_or(unsigned int d) {
  auto &&_sv = elements;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return d;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    return d_a0;
  }
}
