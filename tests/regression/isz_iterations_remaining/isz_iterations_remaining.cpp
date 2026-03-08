#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <isz_iterations_remaining.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int IszIterationsRemaining::isz_iterations(const unsigned int v) {
  if ((v == 0u)) {
    return 16u;
  } else {
    return (((16u - v) > 16u ? 0 : (16u - v)));
  }
}
