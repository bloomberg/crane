#include <algorithm>
#include <fstream>
#include <functional>
#include <hash.h>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

int CHT::max(const int a, const int b) {
  if (a < b) {
    return b;
  } else {
    return a;
  }
}
