#include <nested_record_update_qual.h>

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

std::shared_ptr<Shadow>
NestedRecordUpdateQual::bump(const std::shared_ptr<Shadow> &x) {
  return [&](void) {
    unsigned int n = x->Shadow::value;
    return std::make_shared<Shadow>(Shadow{(n + 1)});
  }();
}
