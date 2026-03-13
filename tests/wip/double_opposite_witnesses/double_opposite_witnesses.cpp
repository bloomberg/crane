#include <double_opposite_witnesses.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<DoubleOppositeWitnessesCase::PreStableCategory>
DoubleOppositeWitnessesCase::opposite_prestable_category(
    std::shared_ptr<DoubleOppositeWitnessesCase::PreStableCategory> pS) {
  return std::make_shared<DoubleOppositeWitnessesCase::PreStableCategory>(
      PreStableCategory{opposite_category(pS->base_category), pS->zero_object,
                        [=](std::any x) mutable { return pS->suspension(x); }});
}
