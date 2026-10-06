#include "hk_carrier_binder_at_concrete_site.h"

holder<bool, box<bool>> run(const holder<Nat, box<Nat>> &m) {
  return Convert_holder::convert(Nat::s(Nat::s(Nat::s(Nat::o()))), m);
}
