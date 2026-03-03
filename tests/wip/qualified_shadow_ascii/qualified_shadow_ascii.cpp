#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <qualified_shadow_ascii.h>
#include <stdexcept>
#include <string>
#include <variant>

Shadow::shadow QualifiedShadowAscii::id_shadow(const Shadow::shadow x) {
  return x;
}
