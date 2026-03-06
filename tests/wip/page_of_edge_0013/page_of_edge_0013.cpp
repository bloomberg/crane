#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <page_of_edge_0013.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>>
PageOfEdge0013::regs(const std::shared_ptr<PageOfEdge0013::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>>
PageOfEdge0013::rom(const std::shared_ptr<PageOfEdge0013::state> &s) {
  return s->rom;
}
