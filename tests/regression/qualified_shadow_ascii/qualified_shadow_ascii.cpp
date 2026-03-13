#include <qualified_shadow_ascii.h>

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

__attribute__((pure)) QualifiedShadowAscii::Shadow::shadow
QualifiedShadowAscii::id_shadow(const QualifiedShadowAscii::Shadow::shadow x) {
  return x;
}
