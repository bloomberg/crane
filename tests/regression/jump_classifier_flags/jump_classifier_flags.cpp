#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <jump_classifier_flags.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

bool JumpClassifierFlags::is_jump(
    const std::shared_ptr<JumpClassifierFlags::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename JumpClassifierFlags::instruction::JCN _args)
                     -> bool { return true; },
                 [](const typename JumpClassifierFlags::instruction::JUN _args)
                     -> bool { return true; },
                 [](const typename JumpClassifierFlags::instruction::JMS _args)
                     -> bool { return true; },
                 [](const typename JumpClassifierFlags::instruction::JIN _args)
                     -> bool { return true; },
                 [](const typename JumpClassifierFlags::instruction::BBL _args)
                     -> bool { return true; },
                 [](const typename JumpClassifierFlags::instruction::ISZ _args)
                     -> bool { return true; },
                 [](const typename JumpClassifierFlags::instruction::ADD _args)
                     -> bool { return false; },
                 [](const typename JumpClassifierFlags::instruction::NOP _args)
                     -> bool { return false; }},
      i->v());
}

unsigned int JumpClassifierFlags::count_jumps(
    const std::shared_ptr<
        List<std::shared_ptr<JumpClassifierFlags::instruction>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<JumpClassifierFlags::instruction>>::nil _args)
              -> unsigned int { return 0; },
          [](const typename List<
              std::shared_ptr<JumpClassifierFlags::instruction>>::cons _args)
              -> unsigned int {
            std::shared_ptr<JumpClassifierFlags::instruction> i = _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<JumpClassifierFlags::instruction>>>
                rest = _args._a1;
            return ([&](void) {
              if (is_jump(std::move(i))) {
                return (0 + 1);
              } else {
                return 0;
              }
            }() + count_jumps(std::move(rest)));
          }},
      prog->v());
}
