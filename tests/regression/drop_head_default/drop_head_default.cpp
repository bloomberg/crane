#include "drop_head_default.h"

unsigned int DropHeadDefault::head_after_drop(const List<unsigned int> &rom,
                                              unsigned int addr) {
  auto &&_sv = drop<unsigned int>(addr, rom);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(_sv.v());
    return a0;
  }
}
