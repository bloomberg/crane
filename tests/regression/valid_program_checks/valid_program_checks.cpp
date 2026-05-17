#include "valid_program_checks.h"

bool ValidProgramChecks::valid_program(const List<uint64_t> &bytes) {
  return ((UINT64_C(2) ? bytes.length() % UINT64_C(2) : bytes.length()) ==
              UINT64_C(0) &&
          bytes.forallb([](uint64_t b) { return b < UINT64_C(256); }));
}
