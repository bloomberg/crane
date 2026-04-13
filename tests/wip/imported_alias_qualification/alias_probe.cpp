#include <alias_probe.h>

#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) AliasSource::cell
AliasSource::id_cell(const std::optional<Player> c) {
  return c;
}
