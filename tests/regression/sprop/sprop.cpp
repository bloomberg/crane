#include "sprop.h"

unsigned int SPropTest::guarded_pred(unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int m = n - 1;
    return m;
  }
}

unsigned int SPropTest::safe_div(unsigned int _x0, unsigned int _x1) {
  return (_x1 ? _x0 / _x1 : 0);
}
