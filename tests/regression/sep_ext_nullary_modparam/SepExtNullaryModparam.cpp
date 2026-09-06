#include "SepExtNullaryModparam.h"

namespace SepExtNullaryModparam {

uint64_t NatAsIntLike::add(uint64_t x0_, uint64_t x1_) { return (x0_ + x1_); }

bool NatAsIntLike::eqb(uint64_t x0_, uint64_t x1_) { return x0_ == x1_; }

} // namespace SepExtNullaryModparam
