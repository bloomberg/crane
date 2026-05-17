#include "jump_targets.h"

List<uint64_t>
JumpTargets::collect_targets(const List<JumpTargets::instr_collection> &prog) {
  if (std::holds_alternative<typename List<JumpTargets::instr_collection>::Nil>(
          prog.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<JumpTargets::instr_collection>::Cons>(prog.v());
    auto _cs = a0.jump_target_collection();
    if (_cs.has_value()) {
      const uint64_t &a = *_cs;
      return List<uint64_t>::cons(a, collect_targets(*a1));
    } else {
      return collect_targets(*a1);
    }
  }
}

bool JumpTargets::addr_in_region(uint64_t addr, const JumpTargets::layout &l) {
  return (l.base_ <= addr && addr < (l.base_ + l.code_));
}

bool JumpTargets::in_layout(const JumpTargets::layout &l,
                            const JumpTargets::instr_region &i) {
  auto _cs = i.jump_target_region();
  if (_cs.has_value()) {
    const uint64_t &a = *_cs;
    return addr_in_region(a, l);
  } else {
    return true;
  }
}

uint64_t JumpTargets::option_nat_or_zero(const std::optional<uint64_t> &o) {
  if (o.has_value()) {
    const uint64_t &n = *o;
    return n;
  } else {
    return UINT64_C(0);
  }
}

uint64_t JumpTargets::target_default(const std::optional<uint64_t> &o) {
  if (o.has_value()) {
    const uint64_t &a = *o;
    return a;
  } else {
    return UINT64_C(0);
  }
}
