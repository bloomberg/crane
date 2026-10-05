#include "valid_program_byte_reject.h"

bool ValidProgramByteReject::valid_program(const List<uint64_t> &bytes) {
  auto &&_once1 = bytes.length();
  return ((UINT64_C(2) ? _once1 % UINT64_C(2) : _once1) == UINT64_C(0) &&
          bytes.forallb([](uint64_t b) { return b < UINT64_C(256); }));
}
