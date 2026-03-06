#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>
#include <writes_regs_classifier.h>

bool WritesRegsClassifier::writes_regs(
    const std::shared_ptr<WritesRegsClassifier::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename WritesRegsClassifier::instruction::XCH _args)
                     -> bool { return true; },
                 [](const typename WritesRegsClassifier::instruction::INC _args)
                     -> bool { return true; },
                 [](const typename WritesRegsClassifier::instruction::FIM _args)
                     -> bool { return true; },
                 [](const typename WritesRegsClassifier::instruction::FIN _args)
                     -> bool { return true; },
                 [](const typename WritesRegsClassifier::instruction::ISZ _args)
                     -> bool { return true; },
                 [](const typename WritesRegsClassifier::instruction::NOP _args)
                     -> bool { return false; },
                 [](const typename WritesRegsClassifier::instruction::ADD _args)
                     -> bool { return false; }},
      i->v());
}

unsigned int WritesRegsClassifier::count_writes_regs(
    const std::shared_ptr<
        List<std::shared_ptr<WritesRegsClassifier::instruction>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<WritesRegsClassifier::instruction>>::nil _args)
              -> unsigned int { return 0; },
          [](const typename List<
              std::shared_ptr<WritesRegsClassifier::instruction>>::cons _args)
              -> unsigned int {
            std::shared_ptr<WritesRegsClassifier::instruction> i = _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<WritesRegsClassifier::instruction>>>
                rest = _args._a1;
            return ([&](void) {
              if (writes_regs(std::move(i))) {
                return (0 + 1);
              } else {
                return 0;
              }
            }() + count_writes_regs(std::move(rest)));
          }},
      prog->v());
}
