#include <canon_struct.h>

#include <any>
#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) bool Bool::eqb(const bool &b1, const bool &b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}
