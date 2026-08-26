#include "list_option_drain.h"

ListOptionDrain::t ListOptionDrain::wrap(uint64_t k, ListOptionDrain::t acc) {
  return t::node(k, List<std::optional<ListOptionDrain::t>>::cons(
                        std::make_optional<ListOptionDrain::t>(std::move(acc)),
                        List<std::optional<ListOptionDrain::t>>::nil()));
}
