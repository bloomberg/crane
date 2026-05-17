#ifndef INCLUDED_IMPORTED_ALIAS_QUALIFICATION
#define INCLUDED_IMPORTED_ALIAS_QUALIFICATION

#include <memory>
#include <optional>

enum class Player { BLACK, WHITE };
using cell = std::optional<Player>;

struct AliasSource {
  static cell id_cell(std::optional<Player> c);
  static inline const cell empty_cell = std::optional<Player>();
};

const cell entry = AliasSource::id_cell(AliasSource::empty_cell);

#endif // INCLUDED_IMPORTED_ALIAS_QUALIFICATION
