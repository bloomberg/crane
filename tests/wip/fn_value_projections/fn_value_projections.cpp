#include "fn_value_projections.h"

List<uint64_t>
FnValueProjections::xs(const List<FnValueProjections::point> &l) {
  return l.template map<uint64_t>(
      [](const FnValueProjections::point &p) { return p.px; });
}

List<uint64_t>
FnValueProjections::firsts(const List<std::pair<uint64_t, uint64_t>> &l) {
  return l.template map<uint64_t>(
      [](std::pair<uint64_t, uint64_t> _x0) -> uint64_t { return _x0.first; });
}

List<std::optional<uint64_t>>
FnValueProjections::somes(const List<uint64_t> &l) {
  return l.template map<std::optional<uint64_t>>(
      [](uint64_t x) { return std::make_optional<uint64_t>(x); });
}

List<uint64_t> FnValueProjections::ids(const List<uint64_t> &l) {
  return l.template map<uint64_t>(Datatypes::template id<uint64_t>);
}

std::any Datatypes::id(std::any x) { return x; }
