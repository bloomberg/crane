#include <even_length_byte_validation.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool EvenLengthByteValidation::valid_program(
    const std::shared_ptr<List<unsigned int>> &bytes) {
  return ((bytes->length() % 2u) == 0u &&
          bytes->forallb([](unsigned int b) { return b < 256u; }));
}
