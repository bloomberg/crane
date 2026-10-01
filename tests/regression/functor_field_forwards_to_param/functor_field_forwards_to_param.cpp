#include "functor_field_forwards_to_param.h"

bool FunctorFieldForwardsToParam::BoolDec::eq_dec(bool x, bool y) {
  if (x) {
    if (y) {
      return true;
    } else {
      return false;
    }
  } else {
    if (y) {
      return false;
    } else {
      return true;
    }
  }
}

bool FunctorFieldForwardsToParam::go(bool x, bool y) {
  if (B::eq_dec(x, y)) {
    return true;
  } else {
    return false;
  }
}

bool FunctorFieldForwardsToParam::go2(bool x, bool y) {
  if (B::eq_dec2(x, y)) {
    return true;
  } else {
    return false;
  }
}
