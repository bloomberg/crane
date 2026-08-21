#include "nested_inductive_no_drain.h"

uint64_t NestedInductiveNoDrain::go(uint64_t n) {
  return tree::node(UINT64_C(0), lst<NestedInductiveNoDrain::tree>::nil())
      .spine(n)
      .tsum();
}
