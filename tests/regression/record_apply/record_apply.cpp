#include <record_apply.h>

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

__attribute__((pure)) unsigned int
RecordApply::apply_record(const std::shared_ptr<RecordApply::R> &r,
                          const unsigned int a, const unsigned int b) {
  return r->f(a, b);
}
