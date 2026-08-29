#include "bool_dec_bde.h"

bool BoolDecBde::eqb_dec(bool a, bool b) {
  if (Bool::bool_dec(a, b)) {
    return true;
  } else {
    return false;
  }
}

bool Bool::bool_dec(bool b1, bool b2) {
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
