#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prom_flagged_sum.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
PromFlaggedSum::flagged_sum(const std::shared_ptr<PromFlaggedSum::state> &s) {
  return ((s->acc + s->prom_addr) + [&](void) {
    if (s->prom_enable) {
      return s->prom_data;
    } else {
      return 0u;
    }
  }());
}
