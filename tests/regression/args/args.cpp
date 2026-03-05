#include <algorithm>
#include <any>
#include <args.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int Args::apply_record(const std::shared_ptr<Args::R> &r,
                                const unsigned int a, const unsigned int b) {
  return r->f(a, b);
}
