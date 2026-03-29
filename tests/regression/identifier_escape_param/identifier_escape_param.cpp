#include <identifier_escape_param.h>

#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
IdentifierEscapeParam::id_from_param(const unsigned int double0) {
  return std::move(double0);
}

__attribute__((pure)) unsigned int
IdentifierEscapeParam::add_one_from_param(const unsigned int double0) {
  return (id_from_param(std::move(double0)) + 1);
}
