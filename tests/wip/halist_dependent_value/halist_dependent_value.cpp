#include "halist_dependent_value.h"

Sig<bool> Sumbool::bool_of_sumbool(bool s) {
  if (s) {
    return Sig<bool>::exist(true);
  } else {
    return Sig<bool>::exist(false);
  }
}
