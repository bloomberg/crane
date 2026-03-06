#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_read_main_edge_0015.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>>
RamReadMainEdge0015::rom(const std::shared_ptr<RamReadMainEdge0015::state> &s) {
  return s->rom;
}
