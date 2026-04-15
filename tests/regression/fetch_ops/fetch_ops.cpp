#include <fetch_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
FetchOps::fetch_byte(const std::shared_ptr<FetchOps::state> &s,
                     const unsigned int addr) {
  return ListDef::template nth<unsigned int>(addr, s->rom, 0u);
}

__attribute__((pure)) unsigned int
FetchOps::fetch_byte_direct(const std::shared_ptr<List<unsigned int>> &rom_data,
                            const unsigned int addr) {
  return ListDef::template nth<unsigned int>(addr, rom_data, 0u);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
FetchOps::fetch_pair(const std::shared_ptr<List<unsigned int>> &rom_data,
                     const unsigned int addr) {
  auto &&_sv = drop<unsigned int>(addr, rom_data);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::make_pair(0u, 0u);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv->v());
    if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
      return std::make_pair(0u, 0u);
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(d_a1->v());
      return std::make_pair(d_a0, d_a00);
    }
  }
}

__attribute__((pure)) std::optional<std::pair<unsigned int, unsigned int>>
FetchOps::fetch_window(const std::shared_ptr<List<unsigned int>> &rom_data,
                       const unsigned int addr) {
  auto &&_sv = drop<unsigned int>(addr, rom_data);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::optional<std::pair<unsigned int, unsigned int>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv->v());
    if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
      return std::optional<std::pair<unsigned int, unsigned int>>();
    } else {
      return std::make_optional<std::pair<unsigned int, unsigned int>>(
          std::make_pair(d_a0, (addr + 2u)));
    }
  }
}
