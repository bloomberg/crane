#include "st_hash_table_test.h"

/// Binds k to k * k for every k of ks.
void insert_squares(t<uint64_t, uint64_t> tbl, const List<uint64_t> &ks) {
  {
    ST::template for_each_with<uint64_t, std::monostate>(
        ks, std::monostate{},
        [=, tbl = std::move(tbl)](std::monostate, uint64_t k) {
          STHashTable::template insert<hashable_nat, uint64_t, uint64_t>(tbl, k,
                                                                         k * k);
          return std::monostate{};
        });
  }
}

/// growth, run in C++.
std::pair<std::pair<std::pair<uint64_t, std::optional<uint64_t>>,
                    std::optional<uint64_t>>,
          List<std::pair<uint64_t, uint64_t>>> growth(uint64_t n) {
  t<uint64_t, uint64_t> tbl =
      STHashTable::template new_sized<uint64_t, uint64_t>(UINT64_C(2));
  insert_squares(tbl, ListDef::seq(UINT64_C(0), n));
  uint64_t s = STHashTable::template size<uint64_t, uint64_t>(tbl);
  std::optional<uint64_t> a =
      STHashTable::template lookup<hashable_nat, uint64_t, uint64_t>(
          tbl, UINT64_C(7));
  std::optional<uint64_t> b =
      STHashTable::template lookup<hashable_nat, uint64_t, uint64_t>(tbl, n);
  return std::make_pair(
      std::make_pair(std::make_pair(s, a), b),
      STHashTable::template to_list<uint64_t, uint64_t>(std::move(tbl)));
}

/// delete_reinsert, run in C++.
std::pair<
    std::pair<std::pair<std::pair<std::optional<uint64_t>, uint64_t>, uint64_t>,
              std::optional<uint64_t>>,
    uint64_t> delete_reinsert() {
  t<uint64_t, uint64_t> tbl = STHashTable::template new0<uint64_t, uint64_t>();
  insert_squares(
      tbl, List<uint64_t>::cons(
               UINT64_C(1),
               List<uint64_t>::cons(
                   UINT64_C(2),
                   List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
  STHashTable::template delete0<hashable_nat, uint64_t, uint64_t>(tbl,
                                                                  UINT64_C(2));
  std::optional<uint64_t> gone =
      STHashTable::template lookup<hashable_nat, uint64_t, uint64_t>(
          tbl, UINT64_C(2));
  uint64_t s1 = STHashTable::template size<uint64_t, uint64_t>(tbl);
  STHashTable::template delete0<hashable_nat, uint64_t, uint64_t>(tbl,
                                                                  UINT64_C(2));
  uint64_t s2 = STHashTable::template size<uint64_t, uint64_t>(tbl);
  STHashTable::template insert<hashable_nat, uint64_t, uint64_t>(
      tbl, UINT64_C(2), UINT64_C(100));
  std::optional<uint64_t> back =
      STHashTable::template lookup<hashable_nat, uint64_t, uint64_t>(
          tbl, UINT64_C(2));
  uint64_t s3 = STHashTable::template size<uint64_t, uint64_t>(std::move(tbl));
  return std::make_pair(
      std::make_pair(std::make_pair(std::make_pair(gone, s1), s2), back), s3);
}

/// Counts one more occurrence of k.
void bump(const t<uint64_t, uint64_t> &tbl, uint64_t k) {
  STHashTable::template alter<hashable_nat, uint64_t, uint64_t>(
      tbl, k, [](std::optional<uint64_t> o) -> std::optional<uint64_t> {
        if (o.has_value()) {
          const uint64_t &c = *o;
          return std::make_optional<uint64_t>((c + 1));
        } else {
          return std::make_optional<uint64_t>(UINT64_C(1));
        }
      });
}

/// counts, run in C++.
std::pair<uint64_t, List<std::pair<uint64_t, uint64_t>>>
counts(const List<uint64_t> &xs) {
  t<uint64_t, uint64_t> tbl =
      STHashTable::template new_sized<uint64_t, uint64_t>(UINT64_C(1));
  ST::template for_each_with<uint64_t, std::monostate>(
      xs, std::monostate{}, [=](std::monostate, uint64_t x) {
        bump(tbl, x);
        return std::monostate{};
      });
  STHashTable::template alter<hashable_nat, uint64_t, uint64_t>(
      tbl, UINT64_C(0),
      [](std::optional<uint64_t>) { return std::optional<uint64_t>(); });
  uint64_t s = STHashTable::template size<uint64_t, uint64_t>(tbl);
  return std::make_pair(
      s, STHashTable::template to_list<uint64_t, uint64_t>(std::move(tbl)));
}

/// fold_iter, run in C++.
std::pair<std::pair<uint64_t, uint64_t>, List<std::pair<uint64_t, uint64_t>>>
fold_iter(const List<std::pair<uint64_t, uint64_t>> &kvs) {
  t<uint64_t, uint64_t> tbl =
      STHashTable::template of_list<hashable_nat, uint64_t, uint64_t>(kvs);
  uint64_t s = STHashTable::template size<uint64_t, uint64_t>(tbl);
  uint64_t total =
      STHashTable::template fold<uint64_t, uint64_t, void, uint64_t>(
          [](uint64_t acc, uint64_t, uint64_t v) { return acc + v; },
          UINT64_C(0),
          tbl);
  t<uint64_t, uint64_t> copy = STHashTable::template new0<uint64_t, uint64_t>();
  STHashTable::template iter<uint64_t, uint64_t>(
      [=](uint64_t k, uint64_t v) {
        STHashTable::template insert<hashable_nat, uint64_t, uint64_t>(
            copy, k, UINT64_C(2) * v);
        return std::monostate{};
      },
      std::move(tbl));
  return std::make_pair(
      std::make_pair(s, total),
      STHashTable::template to_list<uint64_t, uint64_t>(std::move(copy)));
}

/// growth, run in C++.
std::pair<std::pair<std::pair<uint64_t, std::optional<uint64_t>>,
                    std::optional<uint64_t>>,
          List<std::pair<uint64_t, uint64_t>>>
STHashTableTest::growth(uint64_t n) {
  return ::growth(n);
}

/// counts, run in C++.
std::pair<uint64_t, List<std::pair<uint64_t, uint64_t>>>
STHashTableTest::counts(const List<uint64_t> &xs) {
  return ::counts(xs);
}

/// fold_iter, run in C++.
std::pair<std::pair<uint64_t, uint64_t>, List<std::pair<uint64_t, uint64_t>>>
STHashTableTest::fold_iter(const List<std::pair<uint64_t, uint64_t>> &kvs) {
  return ::fold_iter(kvs);
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
