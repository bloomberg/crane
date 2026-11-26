#include "sig_closure_witness_fit.h"

uint64_t SigClosureWitnessFit::use(const crane::fn<List<uint64_t>(bool)> &w) {
  // Precondition: True
  return ((w(true).length() * UINT64_C(10)) + w(false).length());
}
