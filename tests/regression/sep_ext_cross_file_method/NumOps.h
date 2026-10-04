#ifndef INCLUDED_NUMOPS
#define INCLUDED_NUMOPS

#include <variant>

#include "Num.h"

namespace NumOps {

bool leb(const Num::Num &a, const Num::Num &b);
const Num::Num two = Num::Num::succ(Num::Num::succ(Num::Num::zero()));

} // namespace NumOps

#endif // INCLUDED_NUMOPS
