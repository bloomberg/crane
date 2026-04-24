#include <valid_program_byte_reject.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool
ValidProgramByteReject::valid_program(const List<unsigned int> &bytes) {
  return ((2u ? bytes.length() % 2u : bytes.length()) == 0u &&
          bytes.forallb([](const unsigned int &b) { return b < 256u; }));
}
