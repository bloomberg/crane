#include "instance_hoisted_over_qualified.h"

std::pair<Nat, EOUP<List<Nat>>>
InstanceHoistedOverQualified::use(const List<Nat> &bs) {
  return std::make_pair(Eou::helper(Nat::o()), MemoryBytes::bump_all(bs));
}

Nat Eou::helper(Nat n) { return n; }

Nat MemoryBytes::helper0(Nat n) { return n; }

EOUP<List<Nat>> MemoryBytes::bump_all(const List<Nat> &bs) {
  return MemoryBytes::template map_monad<MemoryBytes::EOUP_Monad, Nat, Nat>(
      [](const Nat &b) {
        return Monad0::template ret<MemoryBytes::EOUP_Monad, Nat>(
            MemoryBytes::helper0(b).add(Nat::s(Nat::o())));
      },
      bs);
}
