#include <bool_dec_bde.h>

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

__attribute__((pure)) bool BoolDecBde::eqb_dec(const bool a, const bool b) {
  if (Bool::bool_dec(a, b)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool Bool::bool_dec(const bool b1, const bool b2) {
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
