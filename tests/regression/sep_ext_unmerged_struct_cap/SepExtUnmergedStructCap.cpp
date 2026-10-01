#include "SepExtUnmergedStructCap.h"

#include "Datatypes.h"

namespace SepExtUnmergedStructCap {

Exprs::Expr UseExprs::make_neg(const Exprs::Expr &e) {
  return Exprs::Expr::neg(e);
}

} // namespace SepExtUnmergedStructCap
