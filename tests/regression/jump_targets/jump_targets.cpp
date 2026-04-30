#include <jump_targets.h>

List<unsigned int>
JumpTargets::collect_targets(const List<JumpTargets::instr_collection> &prog) {
  if (std::holds_alternative<typename List<JumpTargets::instr_collection>::Nil>(
          prog.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<JumpTargets::instr_collection>::Cons>(prog.v());
    auto _cs = d_a0.jump_target_collection();
    if (_cs.has_value()) {
      const unsigned int &a = *_cs;
      return List<unsigned int>::cons(a, collect_targets(*(d_a1)));
    } else {
      return collect_targets(*(d_a1));
    }
  }
}

bool JumpTargets::addr_in_region(const unsigned int &addr,
                                 const JumpTargets::layout &l) {
  return (l.base_ <= addr && addr < (l.base_ + l.code_));
}

bool JumpTargets::in_layout(const JumpTargets::layout &l,
                            const JumpTargets::instr_region &i) {
  auto _cs = i.jump_target_region();
  if (_cs.has_value()) {
    const unsigned int &a = *_cs;
    return addr_in_region(a, l);
  } else {
    return true;
  }
}

unsigned int
JumpTargets::option_nat_or_zero(const std::optional<unsigned int> &o) {
  if (o.has_value()) {
    const unsigned int &n = *o;
    return n;
  } else {
    return 0u;
  }
}

unsigned int JumpTargets::target_default(const std::optional<unsigned int> &o) {
  if (o.has_value()) {
    const unsigned int &a = *o;
    return a;
  } else {
    return 0u;
  }
}
