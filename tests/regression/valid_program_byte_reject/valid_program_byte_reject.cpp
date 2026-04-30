#include <valid_program_byte_reject.h>

bool ValidProgramByteReject::valid_program(const List<unsigned int> &bytes) {
  return ((2u ? bytes.length() % 2u : bytes.length()) == 0u &&
          bytes.forallb([](const unsigned int &b) { return b < 256u; }));
}
