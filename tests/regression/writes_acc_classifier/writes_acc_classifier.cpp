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
#include <writes_acc_classifier.h>

bool WritesAccClassifier::writes_acc(
    const std::shared_ptr<WritesAccClassifier::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename WritesAccClassifier::instruction::LDM _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::LD _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::ADD _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::SUB _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::INC _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::XCH _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::BBL _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::SBM _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::RDM _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::RDR _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::ADM _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::RD0 _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::RD1 _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::RD2 _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::RD3 _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::CLB _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::CMA _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::IAC _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::DAC _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::RAL _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::RAR _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::TCC _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::TCS _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::DAA _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::KBP _args)
                     -> bool { return true; },
                 [](const typename WritesAccClassifier::instruction::NOP _args)
                     -> bool { return false; }},
      i->v());
}

unsigned int WritesAccClassifier::count_writes_acc(
    const std::shared_ptr<
        List<std::shared_ptr<WritesAccClassifier::instruction>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<WritesAccClassifier::instruction>>::nil _args)
              -> unsigned int { return 0; },
          [](const typename List<
              std::shared_ptr<WritesAccClassifier::instruction>>::cons _args)
              -> unsigned int {
            std::shared_ptr<WritesAccClassifier::instruction> i = _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<WritesAccClassifier::instruction>>>
                rest = _args._a1;
            return ([&](void) {
              if (writes_acc(std::move(i))) {
                return (0 + 1);
              } else {
                return 0;
              }
            }() + count_writes_acc(std::move(rest)));
          }},
      prog->v());
}
