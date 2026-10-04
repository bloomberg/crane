#include "SepExtEponymousFileRecord.h"

#include "CFG.h"

namespace SepExtEponymousFileRecord {

std::pair<bool, bool> use_it(const CFG::template cfg<bool> &x0_) {
  return CFG::template first_twice<bool>(x0_);
}

} // namespace SepExtEponymousFileRecord
