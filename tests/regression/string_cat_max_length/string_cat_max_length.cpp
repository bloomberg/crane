#include "string_cat_max_length.h"

std::string StringCatMaxLength::double_(uint64_t n, std::string s) {
  if (n <= 0) {
    return s;
  } else {
    uint64_t m = n - 1;
    return double_(m, (s + s).substr(0, 16777211));
  }
}
