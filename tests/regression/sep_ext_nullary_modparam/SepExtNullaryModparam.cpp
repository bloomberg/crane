#include "SepExtNullaryModparam.h"

namespace SepExtNullaryModparam {

unsigned int NatAsIntLike::add(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

bool NatAsIntLike::eqb(const unsigned int _x0, const unsigned int _x1) {
  return _x0 == _x1;
}

} // namespace SepExtNullaryModparam
