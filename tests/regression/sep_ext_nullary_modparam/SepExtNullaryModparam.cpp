#include "SepExtNullaryModparam.h"

namespace SepExtNullaryModparam {

unsigned int NatAsIntLike::add(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}

bool NatAsIntLike::eqb(unsigned int _x0, unsigned int _x1) {
  return _x0 == _x1;
}

} // namespace SepExtNullaryModparam
