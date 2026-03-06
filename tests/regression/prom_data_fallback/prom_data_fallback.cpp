#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prom_data_fallback.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
PromDataFallback::prom_data(const std::shared_ptr<PromDataFallback::state> &s) {
  return s->prom_data;
}

bool PromDataFallback::prom_enable(
    const std::shared_ptr<PromDataFallback::state> &s) {
  return s->prom_enable;
}

unsigned int PromDataFallback::prom_data_or_zero(
    const std::shared_ptr<PromDataFallback::state> &s) {
  if (s->prom_enable) {
    return s->prom_data;
  } else {
    return 0;
  }
}
