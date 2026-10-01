#include "sigt_list_heterogeneous_box.h"

Nat SigtListHeterogeneousBox::count(
    const List<SigT<crane::obj, crane::obj>> &l) {
  return l.length();
}
