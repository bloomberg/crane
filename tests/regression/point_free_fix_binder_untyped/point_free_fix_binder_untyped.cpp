#include "point_free_fix_binder_untyped.h"

std::optional<Tree> go(const Tree &t) {
  return Denote::template freeze<c4n, c3n, c2n, c1n, nat_params, Nat>(t);
}
