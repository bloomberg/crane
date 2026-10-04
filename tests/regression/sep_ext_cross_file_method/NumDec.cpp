#include "NumDec.h"

#include "Num.h"
#include "NumOps.h"

namespace NumDec {

bool num_le_two(const Num::Num &a) { return NumOps::leb(a, NumOps::two); }

} // namespace NumDec
