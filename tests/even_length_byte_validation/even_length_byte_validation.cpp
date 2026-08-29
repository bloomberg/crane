#include "even_length_byte_validation.h"

bool EvenLengthByteValidation::valid_program(const List<uint64_t> &bytes) {
  return ((UINT64_C(2) ? bytes.length() % UINT64_C(2) : bytes.length()) ==
              UINT64_C(0) &&
          bytes.forallb([](uint64_t b) { return b < UINT64_C(256); }));
}
