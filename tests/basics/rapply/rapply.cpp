#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <rapply.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Nat> RApply::apply_record(const std::shared_ptr<RApply::R> &r,
                                          const std::shared_ptr<Nat> &a,
                                          const std::shared_ptr<Nat> &b) {
  return r->f(a, b);
}
