#include "module.h"

Comparison NatOrdered::compare(uint64_t x0_, uint64_t x1_) {
  return (x0_ < x1_ ? Comparison::LT
                    : (x1_ < x0_ ? Comparison::GT : Comparison::EQ));
}
