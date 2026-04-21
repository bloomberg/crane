#include <imported_alias_qualification.h>

#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) cell AliasSource::id_cell(const std::optional<Player> c) {
  return c;
}
