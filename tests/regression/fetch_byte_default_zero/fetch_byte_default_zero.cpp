#include <algorithm>
#include <any>
#include <cassert>
#include <fetch_byte_default_zero.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int FetchByteDefaultZero::fetch_byte(
    const std::shared_ptr<FetchByteDefaultZero::state> &s,
    const unsigned int addr) {
  return s->rom->nth(addr, 0u);
}
