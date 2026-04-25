#include <identifier_escape_param.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int
IdentifierEscapeParam::id_from_param(unsigned int double0) {
  return double0;
}

__attribute__((pure)) unsigned int
IdentifierEscapeParam::add_one_from_param(const unsigned int &double0) {
  return (id_from_param(double0) + 1);
}
