#include "nested_concat_map.h"

List<uint64_t> NestedConcatMap::flatten(const List<List<List<uint64_t>>> &c) {
  return c.template concat<List<uint64_t>>().template concat<uint64_t>();
}

List<List<uint64_t>>
NestedConcatMap::regroup(const List<List<List<uint64_t>>> &c) {
  return c.template map<List<uint64_t>>(
      [](const auto &_x) { return _x.template concat<uint64_t>(); });
}
