#include <bool_dec_bde.h>

#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) bool BoolDecBde::eqb_dec(const bool &a, const bool &b) {
  if (Bool::bool_dec(a, b)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool Bool::bool_dec(const bool &b1, const bool &b2) {
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
