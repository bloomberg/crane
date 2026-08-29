#include "prod_snd_projection.h"

uint64_t ProdSndProjection::depth(const ProdSndProjection::t &x) {
  if (std::holds_alternative<typename ProdSndProjection::t::L>(x.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] = std::get<typename ProdSndProjection::t::N>(x.v());
    return (depth((*a0).second) + 1);
  }
}
