#include "fetch_ops.h"

uint64_t FetchOps::fetch_byte(const FetchOps::state &s, uint64_t addr) {
  return ListDef::template nth<uint64_t>(addr, s.rom, UINT64_C(0));
}

uint64_t FetchOps::fetch_byte_direct(const List<uint64_t> &rom_data,
                                     uint64_t addr) {
  return ListDef::template nth<uint64_t>(addr, rom_data, UINT64_C(0));
}

std::pair<uint64_t, uint64_t>
FetchOps::fetch_pair(const List<uint64_t> &rom_data, uint64_t addr) {
  auto &&_sv = drop<uint64_t>(addr, rom_data);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return std::make_pair(UINT64_C(0), UINT64_C(0));
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return std::make_pair(a0, a00);
    }
  }
}

std::optional<std::pair<uint64_t, uint64_t>>
FetchOps::fetch_window(const List<uint64_t> &rom_data, uint64_t addr) {
  auto &&_sv = drop<uint64_t>(addr, rom_data);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::optional<std::pair<uint64_t, uint64_t>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    auto &&_sv = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
      return std::optional<std::pair<uint64_t, uint64_t>>();
    } else {
      return std::make_optional<std::pair<uint64_t, uint64_t>>(
          std::make_pair(a0, (addr + UINT64_C(2))));
    }
  }
}
