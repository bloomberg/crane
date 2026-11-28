#include "st_hash_table_test.h"

#include <algorithm>
#include <iostream>
#include <utility>
#include <variant>
#include <vector>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

using Entry = std::pair<uint64_t, uint64_t>;

std::vector<Entry> sorted(const List<Entry> &l) {
  std::vector<Entry> out;
  const List<Entry> *cur = &l;
  while (auto *c = std::get_if<List<Entry>::Cons>(&cur->v())) {
    out.push_back(c->a);
    cur = c->l.get();
  }
  std::sort(out.begin(), out.end());
  return out;
}

List<uint64_t> of_vector(const std::vector<uint64_t> &v) {
  List<uint64_t> l = List<uint64_t>::nil();
  for (auto it = v.rbegin(); it != v.rend(); ++it)
    l = List<uint64_t>::cons(*it, std::move(l));
  return l;
}

List<Entry> of_entries(const std::vector<Entry> &v) {
  List<Entry> l = List<Entry>::nil();
  for (auto it = v.rbegin(); it != v.rend(); ++it)
    l = List<Entry>::cons(*it, std::move(l));
  return l;
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // new_sized, insert past the initial size (growth), size, lookup, to_list
  {
    auto [sab, kvs] = STHashTableTest::growth(100);
    auto [sa, b] = sab;
    auto [s, a] = sa;
    ASSERT(s == 100);
    ASSERT(a == std::optional<uint64_t>(49));
    ASSERT(!b.has_value());
    std::vector<Entry> expected;
    for (uint64_t k = 0; k < 100; ++k)
      expected.emplace_back(k, k * k);
    ASSERT(sorted(kvs) == expected);
    std::cout << "growth 100: size " << s << std::endl;
  }
  // new, delete, delete of an absent key, reinsert
  {
    auto [rest, s3] = STHashTableTest::delete_reinsert;
    auto [rest2, back] = rest;
    auto [rest3, s2] = rest2;
    auto [gone, s1] = rest3;
    ASSERT(!gone.has_value());
    ASSERT(s1 == 2);
    ASSERT(s2 == 2);
    ASSERT(back == std::optional<uint64_t>(100));
    ASSERT(s3 == 3);
    std::cout << "delete_reinsert: sizes " << s1 << " " << s2 << " " << s3
              << std::endl;
  }
  // alter: insert, update, and unbind
  {
    auto [s, kvs] = STHashTableTest::counts(of_vector({3, 0, 1, 3, 0, 3, 7}));
    ASSERT(s == 3);
    ASSERT((sorted(kvs) == std::vector<Entry>{{1, 1}, {3, 3}, {7, 1}}));
    std::cout << "counts: " << s << " keys" << std::endl;
  }
  // of_list (later binding wins), fold, iter
  {
    auto [st, kvs] = STHashTableTest::fold_iter(
        of_entries({{1, 10}, {2, 20}, {1, 11}, {30, 5}}));
    auto [s, total] = st;
    ASSERT(s == 3);
    ASSERT(total == 36);
    ASSERT((sorted(kvs) == std::vector<Entry>{{1, 22}, {2, 40}, {30, 10}}));
    std::cout << "fold_iter: size " << s << ", total " << total << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "All st_hash_table_test tests passed!" << std::endl;
  }
  return testStatus;
}
