#include "gadt_index_erasure.h"

/// The evaluator is passed as a function value to map, which instantiates
/// it at nat while its signature still returns std::any.
List<uint64_t>
GadtIndexErasure::evalAll(const List<GadtIndexErasure::expr> &l) {
  return l.template map<uint64_t>([](GadtIndexErasure::expr _ue0) {
    return std::any_cast<uint64_t>(eval<uint64_t>(_ue0));
  });
}
