#ifndef INCLUDED_IDENTIFIER_ESCAPE_PARAM
#define INCLUDED_IDENTIFIER_ESCAPE_PARAM

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct IdentifierEscapeParam {
  __attribute__((pure)) static unsigned int id_from_param(unsigned int double0);
  __attribute__((pure)) static unsigned int
  add_one_from_param(const unsigned int &double0);

  static inline const unsigned int t = add_one_from_param(6u);
};

#endif // INCLUDED_IDENTIFIER_ESCAPE_PARAM
