#include "grammar_tuple_record_cons.h"

bool triples_le_max(const std::deque<rgb> &ts, uint64_t m) {
  if (ts.empty()) {
    return true;
  } else {
    const auto &t = ts.front();
    std::decay_t<decltype(ts)> ts_(ts.begin() + 1, ts.end());
    return (t.red <= m && triples_le_max(ts_, m));
  }
}

uint64_t num_entries(std::monostate) {
  return static_cast<uint64_t>(entries.size());
}
