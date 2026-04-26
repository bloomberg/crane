#include <step_fetch_decode_exec.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
StepFetchDecodeExec::fetch_byte(const StepFetchDecodeExec::state &s,
                                const unsigned int &addr) {
  return ListDef::template nth<unsigned int>(addr, s.rom, 0u);
}

__attribute__((pure)) StepFetchDecodeExec::instruction
StepFetchDecodeExec::decode(const unsigned int &b1, const unsigned int &b2) {
  if ((2u ? b1 % 2u : b1) == 0u) {
    return instruction::nop();
  } else {
    return instruction::add_acc((16u ? b2 % 16u : b2));
  }
}

__attribute__((pure)) StepFetchDecodeExec::state
StepFetchDecodeExec::execute(const StepFetchDecodeExec::state &s,
                             const StepFetchDecodeExec::instruction &i) {
  if (std::holds_alternative<typename StepFetchDecodeExec::instruction::NOP>(
          i.v())) {
    return state{s.acc, (s.pc + 1u), s.rom};
  } else {
    const auto &[d_a0] =
        std::get<typename StepFetchDecodeExec::instruction::ADD_ACC>(i.v());
    return state{(16u ? (s.acc + d_a0) % 16u : (s.acc + d_a0)), (s.pc + 2u),
                 s.rom};
  }
}

__attribute__((pure)) StepFetchDecodeExec::state
StepFetchDecodeExec::step(const StepFetchDecodeExec::state &s) {
  unsigned int b1 = fetch_byte(s, s.pc);
  unsigned int b2 = fetch_byte(s, (s.pc + 1u));
  return execute(s, decode(b1, b2));
}
