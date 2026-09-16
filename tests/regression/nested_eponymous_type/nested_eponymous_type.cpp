#include "nested_eponymous_type.h"

bool Other::is_lt(const Nat &n) {
  return n.ltb(Nat::s(Nat::s(Nat::s(Nat::o()))));
}

bool Compare_Mod::is_lt0(const Nat &n) {
  return n.ltb(Nat::s(Nat::s(Nat::s(Nat::o()))));
}
