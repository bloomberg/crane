#include <cassert>
#include <expanded_product_wrong_class_field.h>

struct PV {
  using provenance = uint64_t;
  using allocationId = uint64_t;
  using prov = uint64_t;
  static prov no_prov() { return 0; }
  static provenance a_provenance() { return 1; }
  static allocationId an_allocationId() { return 2; }
};

struct PT {
  using ptr = uint64_t;
  static ptr zero_ptr() { return 7; }
};

struct P {
  using PROV = PV;
  using PTR = PT;
};

int main() {
  assert(ExpandedProductWrongClassField::use<P>() == 7);
  return 0;
}
