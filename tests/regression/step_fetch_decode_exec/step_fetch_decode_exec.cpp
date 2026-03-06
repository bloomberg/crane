#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <step_fetch_decode_exec.h>
#include <string>
#include <utility>
#include <variant>

unsigned int
StepFetchDecodeExec::acc(const std::shared_ptr<StepFetchDecodeExec::state> &s) {
  return s->acc;
}

unsigned int
StepFetchDecodeExec::pc(const std::shared_ptr<StepFetchDecodeExec::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>>
StepFetchDecodeExec::rom(const std::shared_ptr<StepFetchDecodeExec::state> &s) {
  return s->rom;
}

unsigned int StepFetchDecodeExec::fetch_byte(
    const std::shared_ptr<StepFetchDecodeExec::state> &s,
    const unsigned int addr) {
  return s->rom->nth(addr, 0);
}

std::shared_ptr<StepFetchDecodeExec::instruction>
StepFetchDecodeExec::decode(const unsigned int b1, const unsigned int b2) {
  if (((b1 % ((0 + 1) + 1)) == 0)) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::ADD_ACC_(
        (std::move(b2) %
         ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1)));
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
                state{s->acc, (s->pc + (0 + 1)), s->rom});
          },
          [&](const typename StepFetchDecodeExec::instruction::ADD_ACC _args)
              -> std::shared_ptr<StepFetchDecodeExec::state> {
            unsigned int n = _args._a0;
            return std::make_shared<StepFetchDecodeExec::state>(state{
                ((s->acc + std::move(n)) %
                 ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1)),
                (s->pc + ((0 + 1) + 1)), s->rom});
          }},
      i->v());
}

std::shared_ptr<StepFetchDecodeExec::state> StepFetchDecodeExec::step(
    const std::shared_ptr<StepFetchDecodeExec::state> &s) {
  unsigned int b1 = fetch_byte(s, s->pc);
  unsigned int b2 = fetch_byte(s, (s->pc + (0 + 1)));
  return execute(s, decode(std::move(b1), std::move(b2)));
}
