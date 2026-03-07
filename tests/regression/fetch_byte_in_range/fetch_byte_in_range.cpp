#include <algorithm>
#include <any>
#include <cassert>
#include <fetch_byte_in_range.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
FetchByteInRange::fetch_byte(const std::shared_ptr<List<unsigned int>> &rom,
                             const unsigned int addr) {
  return rom->nth(addr, 0);
}
