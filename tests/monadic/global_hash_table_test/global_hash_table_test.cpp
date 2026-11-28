#include "global_hash_table_test.h"

/// Binds k to k * k for every k of ks.
void insert_squares(t<uint64_t, uint64_t> tbl, const List<uint64_t> &ks) {
  {
    ST::template for_each_with<uint64_t, std::monostate>(
        ks, std::monostate{},
        [=, tbl = std::move(tbl)](std::monostate, uint64_t k) {
          GlobalHashTable::template insert<hashable_nat, uint64_t, uint64_t>(
              tbl, k, k * k);
          return std::monostate{};
        });
  }
}

/// growth, in C++.
std::pair<std::pair<std::pair<uint64_t, std::optional<uint64_t>>,
                    std::optional<uint64_t>>,
          List<std::pair<uint64_t, uint64_t>>> growth(uint64_t n) {
  t<uint64_t, uint64_t> tbl =
      GlobalHashTable::template new_sized<uint64_t, uint64_t>(UINT64_C(2));
  insert_squares(tbl, ListDef::seq(UINT64_C(0), n));
  uint64_t s = GlobalHashTable::template size<uint64_t, uint64_t>(tbl);
  std::optional<uint64_t> a =
      GlobalHashTable::template lookup<hashable_nat, uint64_t, uint64_t>(
          tbl, UINT64_C(7));
  std::optional<uint64_t> b =
      GlobalHashTable::template lookup<hashable_nat, uint64_t, uint64_t>(tbl,
                                                                         n);
  return std::make_pair(
      std::make_pair(std::make_pair(s, a), b),
      GlobalHashTable::template to_list<uint64_t, uint64_t>(std::move(tbl)));
}

/// delete_reinsert, in C++.
std::pair<
    std::pair<std::pair<std::pair<std::optional<uint64_t>, uint64_t>, uint64_t>,
              std::optional<uint64_t>>,
    uint64_t> delete_reinsert() {
  t<uint64_t, uint64_t> tbl =
      GlobalHashTable::template new0<uint64_t, uint64_t>();
  insert_squares(
      tbl, List<uint64_t>::cons(
               UINT64_C(1),
               List<uint64_t>::cons(
                   UINT64_C(2),
                   List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
  GlobalHashTable::template delete0<hashable_nat, uint64_t, uint64_t>(
      tbl, UINT64_C(2));
  std::optional<uint64_t> gone =
      GlobalHashTable::template lookup<hashable_nat, uint64_t, uint64_t>(
          tbl, UINT64_C(2));
  uint64_t s1 = GlobalHashTable::template size<uint64_t, uint64_t>(tbl);
  GlobalHashTable::template delete0<hashable_nat, uint64_t, uint64_t>(
      tbl, UINT64_C(2));
  uint64_t s2 = GlobalHashTable::template size<uint64_t, uint64_t>(tbl);
  GlobalHashTable::template insert<hashable_nat, uint64_t, uint64_t>(
      tbl, UINT64_C(2), UINT64_C(100));
  std::optional<uint64_t> back =
      GlobalHashTable::template lookup<hashable_nat, uint64_t, uint64_t>(
          tbl, UINT64_C(2));
  uint64_t s3 =
      GlobalHashTable::template size<uint64_t, uint64_t>(std::move(tbl));
  return std::make_pair(
      std::make_pair(std::make_pair(std::make_pair(gone, s1), s2), back), s3);
}

/// Counts one more occurrence of k.
void bump(const t<uint64_t, uint64_t> &tbl, uint64_t k) {
  GlobalHashTable::template alter<hashable_nat, uint64_t, uint64_t>(
      tbl, k, [](std::optional<uint64_t> o) -> std::optional<uint64_t> {
        if (o.has_value()) {
          const uint64_t &c = *o;
          return std::make_optional<uint64_t>((c + 1));
        } else {
          return std::make_optional<uint64_t>(UINT64_C(1));
        }
      });
}

/// counts, in C++.
std::pair<uint64_t, List<std::pair<uint64_t, uint64_t>>>
counts(const List<uint64_t> &xs) {
  t<uint64_t, uint64_t> tbl =
      GlobalHashTable::template new_sized<uint64_t, uint64_t>(UINT64_C(1));
  ST::template for_each_with<uint64_t, std::monostate>(
      xs, std::monostate{}, [=](std::monostate, uint64_t x) {
        bump(tbl, x);
        return std::monostate{};
      });
  GlobalHashTable::template alter<hashable_nat, uint64_t, uint64_t>(
      tbl, UINT64_C(0),
      [](std::optional<uint64_t>) { return std::optional<uint64_t>(); });
  uint64_t s = GlobalHashTable::template size<uint64_t, uint64_t>(tbl);
  return std::make_pair(
      s, GlobalHashTable::template to_list<uint64_t, uint64_t>(std::move(tbl)));
}

/// fold_iter, in C++.
std::pair<std::pair<uint64_t, uint64_t>, List<std::pair<uint64_t, uint64_t>>>
fold_iter(const List<std::pair<uint64_t, uint64_t>> &kvs) {
  t<uint64_t, uint64_t> tbl =
      GlobalHashTable::template of_list<hashable_nat, uint64_t, uint64_t>(kvs);
  uint64_t s = GlobalHashTable::template size<uint64_t, uint64_t>(tbl);
  uint64_t total = GlobalHashTable::template fold<uint64_t, uint64_t, uint64_t>(
      [](uint64_t acc, uint64_t, uint64_t v) { return acc + v; },
      UINT64_C(0),
      tbl);
  t<uint64_t, uint64_t> copy =
      GlobalHashTable::template new0<uint64_t, uint64_t>();
  GlobalHashTable::template iter<uint64_t, uint64_t>(
      [=](uint64_t k, uint64_t v) {
        GlobalHashTable::template insert<hashable_nat, uint64_t, uint64_t>(
            copy, k, UINT64_C(2) * v);
        return std::monostate{};
      },
      std::move(tbl));
  return std::make_pair(
      std::make_pair(s, total),
      GlobalHashTable::template to_list<uint64_t, uint64_t>(std::move(copy)));
}

/// growth, in C++.
std::pair<std::pair<std::pair<uint64_t, std::optional<uint64_t>>,
                    std::optional<uint64_t>>,
          List<std::pair<uint64_t, uint64_t>>>
GlobalHashTableTest::growth(uint64_t x0_) {
  return ::growth(x0_);
}

/// delete_reinsert, in C++.
std::pair<
    std::pair<std::pair<std::pair<std::optional<uint64_t>, uint64_t>, uint64_t>,
              std::optional<uint64_t>>,
    uint64_t> GlobalHashTableTest::delete_reinsert() {
  return ::delete_reinsert();
}

/// counts, in C++.
std::pair<uint64_t, List<std::pair<uint64_t, uint64_t>>>
GlobalHashTableTest::counts(const List<uint64_t> &x0_) {
  return ::counts(x0_);
}

/// fold_iter, in C++.
std::pair<std::pair<uint64_t, uint64_t>, List<std::pair<uint64_t, uint64_t>>>
GlobalHashTableTest::fold_iter(const List<std::pair<uint64_t, uint64_t>> &x0_) {
  return ::fold_iter(x0_);
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
