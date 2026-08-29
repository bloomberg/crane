#include "step_fetch_decode_exec.h"

uint64_t StepFetchDecodeExec::fetch_byte(const StepFetchDecodeExec::state &s,
                                         uint64_t addr) {
  return ListDef::template nth<uint64_t>(addr, s.rom, UINT64_C(0));
}

StepFetchDecodeExec::instruction StepFetchDecodeExec::decode(uint64_t b1,
                                                             uint64_t b2) {
  if ((UINT64_C(2) ? b1 % UINT64_C(2) : b1) == UINT64_C(0)) {
    return instruction::nop();
  } else {
    return instruction::add_acc((UINT64_C(16) ? b2 % UINT64_C(16) : b2));
  }
}

StepFetchDecodeExec::state
StepFetchDecodeExec::execute(const StepFetchDecodeExec::state &s,
                             const StepFetchDecodeExec::instruction &i) {
  if (std::holds_alternative<typename StepFetchDecodeExec::instruction::NOP>(
          i.v())) {
    return state{s.acc, (s.pc + UINT64_C(1)), s.rom};
  } else {
    const auto &[a0] =
        std::get<typename StepFetchDecodeExec::instruction::ADD_ACC>(i.v());
    return state{(UINT64_C(16) ? (s.acc + a0) % UINT64_C(16) : (s.acc + a0)),
                 (s.pc + UINT64_C(2)), s.rom};
  }
}

StepFetchDecodeExec::state
StepFetchDecodeExec::step(const StepFetchDecodeExec::state &s) {
  uint64_t b1 = fetch_byte(s, s.pc);
  uint64_t b2 = fetch_byte(s, (s.pc + UINT64_C(1)));
  return execute(s, decode(b1, b2));
}
