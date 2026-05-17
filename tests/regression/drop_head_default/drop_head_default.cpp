#include "drop_head_default.h"

uint64_t DropHeadDefault::head_after_drop(const List<uint64_t> &rom,
                                          uint64_t addr) {
  auto &&_sv = drop<uint64_t>(addr, rom);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    return a0;
  }
}
