#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <mkstate_signature_drift.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int MkstateSignatureDrift::score(const MkstateSignatureDrift::item x) {
  return [&](void) {
    switch (x) {
    case item::S_: {
      return (0 + 1);
    }
    case item::S_0: {
      return ((0 + 1) + 1);
    }
    }
  }();
}
