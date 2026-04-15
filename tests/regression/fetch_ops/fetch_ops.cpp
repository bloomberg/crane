#include <fetch_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
FetchOps::fetch_byte(const std::shared_ptr<FetchOps::state> &s,
                     const unsigned int addr) {
  return s->rom->nth(addr, 0u);
}

__attribute__((pure)) unsigned int
FetchOps::fetch_byte_direct(const std::shared_ptr<List<unsigned int>> &rom_data,
                            const unsigned int addr) {
  return rom_data->nth(addr, 0u);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
FetchOps::fetch_pair(const std::shared_ptr<List<unsigned int>> &rom_data,
                     const unsigned int addr) {
  auto &&_sv = drop<unsigned int>(addr, rom_data);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::make_pair(0u, 0u);
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return std::make_pair(0u, 0u);
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      return std::make_pair(_m.d_a0, _m0.d_a0);
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
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    auto &&_sv = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
      return std::optional<std::pair<unsigned int, unsigned int>>();
    } else {
      return std::make_optional<std::pair<unsigned int, unsigned int>>(
          std::make_pair(_m.d_a0, (addr + 2u)));
    }
  }
}
