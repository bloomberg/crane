// A record named, up to case, like its file (cfg in CFG.v).  Separate
// extraction emits the file as `namespace CFG` holding `struct cfg` and the
// file's functions as free functions beside it; first_twice must call
// `first`, not `Cfg<int>::first` as if the file had been merged into the
// record.
#include "Datatypes.h"
#include "CFG.h"
#include "SepExtEponymousFileRecord.h"

#include <cassert>

int main() {
  CFG::cfg<bool> c{true, Datatypes::List<bool>::nil()};
  auto r = SepExtEponymousFileRecord::use_it(c);
  assert(r.first && r.second);
  return 0;
}
