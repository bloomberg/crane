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

std::shared_ptr<
    DoubleOppositeWitnessesCase::Path<DoubleOppositeWitnessesCase::Obj>>
DoubleOppositeWitnessesCase::left_witness(
    const DoubleOppositeWitnessesCase::Obj _x0) {
  return identity_witnesses.first(_x0);
}

std::shared_ptr<
    DoubleOppositeWitnessesCase::Path<DoubleOppositeWitnessesCase::Obj>>
DoubleOppositeWitnessesCase::right_witness(
    const DoubleOppositeWitnessesCase::Obj _x0) {
  return identity_witnesses.second(_x0);
}
