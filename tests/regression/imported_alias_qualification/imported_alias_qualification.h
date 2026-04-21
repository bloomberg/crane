#ifndef INCLUDED_IMPORTED_ALIAS_QUALIFICATION
#define INCLUDED_IMPORTED_ALIAS_QUALIFICATION

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Player { e_BLACK, e_WHITE };
using cell = std::optional<Player>;

struct AliasSource {
  __attribute__((pure)) static cell id_cell(const std::optional<Player> c);
  static inline const cell empty_cell = std::optional<Player>();
};

const cell entry = AliasSource::id_cell(AliasSource::empty_cell);

#endif // INCLUDED_IMPORTED_ALIAS_QUALIFICATION
