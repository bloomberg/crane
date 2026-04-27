#include <even_length_byte_validation.h>

__attribute__((pure)) bool
EvenLengthByteValidation::valid_program(const List<unsigned int> &bytes) {
  return ((2u ? bytes.length() % 2u : bytes.length()) == 0u &&
          bytes.forallb([](const unsigned int &b) { return b < 256u; }));
}
