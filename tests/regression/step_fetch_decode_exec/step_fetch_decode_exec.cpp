#include <step_fetch_decode_exec.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int StepFetchDecodeExec::fetch_byte(
    const std::shared_ptr<StepFetchDecodeExec::state> &s,
    const unsigned int addr) {
  return s->rom->nth(addr, 0u);
}

std::shared_ptr<StepFetchDecodeExec::instruction>
StepFetchDecodeExec::decode(const unsigned int b1, const unsigned int b2) {
  if ((2u ? b1 % 2u : b1) == 0u) {
    return instruction::nop();
  } else {
    return instruction::add_acc((16u ? b2 % 16u : b2));
  }
}

std::shared_ptr<StepFetchDecodeExec::state> StepFetchDecodeExec::execute(
    std::shared_ptr<StepFetchDecodeExec::state> s,
    const std::shared_ptr<StepFetchDecodeExec::instruction> &i) {
  return std::visit(
      Overloaded{
          [&](const typename StepFetchDecodeExec::instruction::NOP _args)
              -> std::shared_ptr<StepFetchDecodeExec::state> {
            return std::make_shared<StepFetchDecodeExec::state>(
                state{s->acc, (s->pc + 1u), s->rom});
          },
          [&](const typename StepFetchDecodeExec::instruction::ADD_ACC _args)
              -> std::shared_ptr<StepFetchDecodeExec::state> {
            return std::make_shared<StepFetchDecodeExec::state>(state{
                (16u ? (s->acc + _args.d_a0) % 16u : (s->acc + _args.d_a0)),
                (s->pc + 2u), s->rom});
          }},
      i->v());
}

std::shared_ptr<StepFetchDecodeExec::state> StepFetchDecodeExec::step(
    const std::shared_ptr<StepFetchDecodeExec::state> &s) {
  unsigned int b1 = fetch_byte(s, s->pc);
  unsigned int b2 = fetch_byte(s, (s->pc + 1u));
  return execute(s, decode(b1, b2));
}
