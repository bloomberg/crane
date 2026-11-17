// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <custom_signature_type_include.h>
#include <cassert>

int main() {
  assert(CustomSignatureTypeInclude::is_real(true));
  assert(CustomSignatureTypeInclude::is_real(false));
  return 0;
}
