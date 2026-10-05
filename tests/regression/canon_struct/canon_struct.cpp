#include "canon_struct.h"

bool Bool::eqb(bool b1, bool b2) {
  if (b1) {
    return b2;
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}
