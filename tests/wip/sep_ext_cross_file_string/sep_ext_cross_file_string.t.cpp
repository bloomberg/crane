// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: When a module type uses Rocq's `string` type, the generated concept
// must qualify it as String::String (not bare String) in separate extraction.

#include "SepExtCrossFileString.h"
#include "Datatypes.h"
#include "String.h"

int main() {
  const auto r = SepExtCrossFileString::ShowNat::show(Datatypes::Nat::s(Datatypes::Nat::o()));
  (void)r;
  return 0;
}
