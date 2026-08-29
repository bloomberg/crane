#include "SepExtUnmergedStructCap.h"

#include "Datatypes.h"

namespace SepExtUnmergedStructCap {

Exprs::Expr UseExprs::make_neg(Exprs::Expr e) {
  return Exprs::Expr::neg(std::move(e));
}

} // namespace SepExtUnmergedStructCap
