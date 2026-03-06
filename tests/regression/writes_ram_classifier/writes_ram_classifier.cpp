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
#include <writes_ram_classifier.h>

bool WritesRamClassifier::writes_ram(
    const std::shared_ptr<WritesRamClassifier::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename WritesRamClassifier::instruction::WRM _args)
                     -> bool { return true; },
                 [](const typename WritesRamClassifier::instruction::WMP _args)
                     -> bool { return true; },
                 [](const typename WritesRamClassifier::instruction::WR0 _args)
                     -> bool { return true; },
                 [](const typename WritesRamClassifier::instruction::WR1 _args)
                     -> bool { return true; },
                 [](const typename WritesRamClassifier::instruction::WR2 _args)
                     -> bool { return true; },
                 [](const typename WritesRamClassifier::instruction::WR3 _args)
                     -> bool { return true; },
                 [](const typename WritesRamClassifier::instruction::NOP _args)
                     -> bool { return false; },
                 [](const typename WritesRamClassifier::instruction::ADD _args)
                     -> bool { return false; }},
      i->v());
}

unsigned int WritesRamClassifier::count_writes_ram(
    const std::shared_ptr<
        List<std::shared_ptr<WritesRamClassifier::instruction>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<WritesRamClassifier::instruction>>::nil _args)
              -> unsigned int { return 0; },
          [](const typename List<
              std::shared_ptr<WritesRamClassifier::instruction>>::cons _args)
              -> unsigned int {
            std::shared_ptr<WritesRamClassifier::instruction> i = _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<WritesRamClassifier::instruction>>>
                rest = _args._a1;
            return ([&](void) {
              if (writes_ram(std::move(i))) {
                return (0 + 1);
              } else {
                return 0;
              }
            }() + count_writes_ram(std::move(rest)));
          }},
      prog->v());
}
