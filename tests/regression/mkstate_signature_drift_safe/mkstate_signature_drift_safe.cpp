#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <mkstate_signature_drift_safe.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
MkstateSignatureDriftSafe::score(const MkstateSignatureDriftSafe::state x) {
  return [&](void) {
    switch (x) {
    case state::S0: {
      return (0 + 1);
    }
    case state::S1: {
      return ((0 + 1) + 1);
    }
    }
  }();
}
