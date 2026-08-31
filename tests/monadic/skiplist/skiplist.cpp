#include "skiplist.h"

bool skiplist_test::nat_lt(uint64_t _x0, uint64_t _x1) { return _x0 < _x1; }

bool skiplist_test::nat_eq(uint64_t _x0, uint64_t _x1) { return _x0 == _x1; }

bool skiplist_test::stm_test_insert_lookup() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(2));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(1));
  sl.insert(nat_lt, nat_eq, UINT64_C(7), UINT64_C(70), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(1), UINT64_C(10), UINT64_C(1));
  std::optional<uint64_t> v5 = sl.lookup(nat_lt, nat_eq, UINT64_C(5));
  std::optional<uint64_t> v3 = sl.lookup(nat_lt, nat_eq, UINT64_C(3));
  std::optional<uint64_t> v7 = sl.lookup(nat_lt, nat_eq, UINT64_C(7));
  std::optional<uint64_t> v1 = sl.lookup(nat_lt, nat_eq, UINT64_C(1));
  std::optional<uint64_t> v9 = sl.lookup(nat_lt, nat_eq, UINT64_C(9));
  bool c1;
  if (v5.has_value()) {
    const uint64_t &n = *v5;
    c1 = n == UINT64_C(50);
  } else {
    c1 = false;
  }
  bool c2;
  if (v3.has_value()) {
    const uint64_t &n = *v3;
    c2 = n == UINT64_C(30);
  } else {
    c2 = false;
  }
  bool c3;
  if (v7.has_value()) {
    const uint64_t &n = *v7;
    c3 = n == UINT64_C(70);
  } else {
    c3 = false;
  }
  bool c4;
  if (v1.has_value()) {
    const uint64_t &n = *v1;
    c4 = n == UINT64_C(10);
  } else {
    c4 = false;
  }
  bool c5;
  if (v9.has_value()) {
    const uint64_t &_x3 = *v9;
    c5 = false;
  } else {
    c5 = true;
  }
  return (c1 && (c2 && (c3 && (c4 && c5))));
}

bool skiplist_test::stm_test_delete() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(2));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(1));
  sl.insert(nat_lt, nat_eq, UINT64_C(7), UINT64_C(70), UINT64_C(0));
  sl.remove(nat_lt, nat_eq, UINT64_C(5));
  std::optional<uint64_t> v5 = sl.lookup(nat_lt, nat_eq, UINT64_C(5));
  std::optional<uint64_t> v3 = sl.lookup(nat_lt, nat_eq, UINT64_C(3));
  std::optional<uint64_t> v7 = sl.lookup(nat_lt, nat_eq, UINT64_C(7));
  bool c1;
  if (v5.has_value()) {
    const uint64_t &_x3 = *v5;
    c1 = false;
  } else {
    c1 = true;
  }
  bool c2;
  if (v3.has_value()) {
    const uint64_t &n = *v3;
    c2 = n == UINT64_C(30);
  } else {
    c2 = false;
  }
  bool c3;
  if (v7.has_value()) {
    const uint64_t &n = *v7;
    c3 = n == UINT64_C(70);
  } else {
    c3 = false;
  }
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_update() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), 500u, UINT64_C(0));
  std::optional<uint64_t> v = sl.lookup(nat_lt, nat_eq, UINT64_C(5));
  return [=]() mutable -> bool {
    if (v.has_value()) {
      const uint64_t &n = *v;
      return n == 500u;
    } else {
      return false;
    }
  }();
}

bool skiplist_test::stm_test_minimum() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(7), UINT64_C(70), UINT64_C(0));
  std::optional<std::pair<uint64_t, uint64_t>> minOpt = sl.minimum();
  return [=]() mutable -> bool {
    if (minOpt.has_value()) {
      const std::pair<uint64_t, uint64_t> &p = *minOpt;
      const auto &[k, v] = p;
      return (k == UINT64_C(3) && v == UINT64_C(30));
    } else {
      return false;
    }
  }();
}

bool skiplist_test::stm_test_length_isEmpty() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  bool empty1 = sl.isEmpty();
  uint64_t len1 = sl.length();
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  bool empty2 = sl.isEmpty();
  uint64_t len2 = sl.length();
  bool c2 = len1 == UINT64_C(0);
  bool c3 = !(empty2);
  bool c4 = len2 == UINT64_C(2);
  return (empty1 && (c2 && (c3 && c4)));
}

bool skiplist_test::stm_test_front_back() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(7), UINT64_C(70), UINT64_C(0));
  std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> frontOpt =
      sl.front();
  std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> backOpt =
      sl.back();
  bool c1;
  if (frontOpt.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p = *frontOpt;
    c1 = SkipList<int, int>::template key<uint64_t, uint64_t>(p) == UINT64_C(3);
  } else {
    c1 = false;
  }
  bool c2;
  if (backOpt.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p = *backOpt;
    c2 = SkipList<int, int>::template key<uint64_t, uint64_t>(p) == UINT64_C(7);
  } else {
    c2 = false;
  }
  return (c1 && c2);
}

bool skiplist_test::stm_test_popFront() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(7), UINT64_C(70), UINT64_C(0));
  std::optional<std::pair<uint64_t, uint64_t>> pop1 = sl.popFront();
  std::optional<std::pair<uint64_t, uint64_t>> pop2 = sl.popFront();
  uint64_t len = sl.length();
  bool c1;
  if (pop1.has_value()) {
    const std::pair<uint64_t, uint64_t> &p = *pop1;
    const auto &[k, v] = p;
    c1 = (k == UINT64_C(3) && v == UINT64_C(30));
  } else {
    c1 = false;
  }
  bool c2;
  if (pop2.has_value()) {
    const std::pair<uint64_t, uint64_t> &p = *pop2;
    const auto &[k, v] = p;
    c2 = (k == UINT64_C(5) && v == UINT64_C(50));
  } else {
    c2 = false;
  }
  bool c3 = len == UINT64_C(1);
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_addUnique() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  bool r1 =
      sl.addUnique(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  bool r2 = sl.addUnique(nat_lt, nat_eq, UINT64_C(5), 500u, UINT64_C(0));
  bool r3 =
      sl.addUnique(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  std::optional<uint64_t> v5 = sl.lookup(nat_lt, nat_eq, UINT64_C(5));
  uint64_t len = sl.length();
  bool c2 = !(r2);
  bool c4;
  if (v5.has_value()) {
    const uint64_t &n = *v5;
    c4 = n == UINT64_C(50);
  } else {
    c4 = false;
  }
  bool c5 = len == UINT64_C(2);
  return (r1 && (c2 && (r3 && (c4 && c5))));
}

bool skiplist_test::stm_test_find() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> pairOpt =
      sl.find(nat_lt, nat_eq, UINT64_C(5));
  std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> noneOpt =
      sl.find(nat_lt, nat_eq, UINT64_C(9));
  bool c1;
  if (pairOpt.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p = *pairOpt;
    uint64_t k = SkipList<int, int>::template key<uint64_t, uint64_t>(p);
    c1 = k == UINT64_C(5);
  } else {
    c1 = false;
  }
  bool c2;
  if (noneOpt.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &_x1 = *noneOpt;
    c2 = false;
  } else {
    c2 = true;
  }
  return (c1 && c2);
}

bool skiplist_test::stm_test_navigation() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(1), UINT64_C(10), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> frontOpt =
      sl.front();
  if (frontOpt.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &first = *frontOpt;
    std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> nextOpt =
        SkipList<int, int>::template next<uint64_t, uint64_t>(first);
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &second = *nextOpt;
      std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> prevOpt =
          std::move(sl).previous(nat_eq, second);
      bool c1 = SkipList<int, int>::template key<uint64_t, uint64_t>(first) ==
                UINT64_C(1);
      bool c2 = SkipList<int, int>::template key<uint64_t, uint64_t>(second) ==
                UINT64_C(3);
      bool c3;
      if (prevOpt.has_value()) {
        const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p = *prevOpt;
        c3 = SkipList<int, int>::template key<uint64_t, uint64_t>(p) ==
             UINT64_C(1);
      } else {
        c3 = false;
      }
      return (c1 && (c2 && c3));
    } else {
      return false;
    }
  } else {
    return false;
  }
}

bool skiplist_test::stm_test_bounds() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(2), UINT64_C(20), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(4), UINT64_C(40), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(6), UINT64_C(60), UINT64_C(0));
  std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> lb3 =
      sl.findLowerBound(nat_lt, UINT64_C(3));
  std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> lb4 =
      sl.findLowerBound(nat_lt, UINT64_C(4));
  std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>> ub4 =
      sl.findUpperBound(nat_lt, nat_eq, UINT64_C(4));
  bool c1;
  if (lb3.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p = *lb3;
    c1 = SkipList<int, int>::template key<uint64_t, uint64_t>(p) == UINT64_C(4);
  } else {
    c1 = false;
  }
  bool c2;
  if (lb4.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p = *lb4;
    c2 = SkipList<int, int>::template key<uint64_t, uint64_t>(p) == UINT64_C(4);
  } else {
    c2 = false;
  }
  bool c3;
  if (ub4.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p = *ub4;
    c3 = SkipList<int, int>::template key<uint64_t, uint64_t>(p) == UINT64_C(6);
  } else {
    c3 = false;
  }
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_removeAll() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  sl.insert(nat_lt, nat_eq, UINT64_C(7), UINT64_C(70), UINT64_C(0));
  uint64_t count = sl.removeAll();
  bool empty = sl.isEmpty();
  uint64_t len = sl.length();
  bool c1 = count == UINT64_C(3);
  bool c3 = len == UINT64_C(0);
  return (c1 && (empty && c3));
}

bool skiplist_test::stm_test_bde_api() {
  SkipList<uint64_t, uint64_t> sl =
      SkipList<int, int>::template create<uint64_t, uint64_t>(UINT64_C(0),
                                                              UINT64_C(0));
  std::pair<std::shared_ptr<SkipNode<uint64_t, uint64_t>>, bool> result1 =
      sl.bde_add(nat_lt, nat_eq, UINT64_C(5), UINT64_C(50), UINT64_C(0));
  auto [_x, front1] = std::move(result1);
  std::pair<std::shared_ptr<SkipNode<uint64_t, uint64_t>>, bool> result2 =
      sl.bde_add(nat_lt, nat_eq, UINT64_C(3), UINT64_C(30), UINT64_C(0));
  auto [_x0, front2] = std::move(result2);
  std::pair<std::shared_ptr<SkipNode<uint64_t, uint64_t>>, bool> result3 =
      sl.bde_add(nat_lt, nat_eq, UINT64_C(7), UINT64_C(70), UINT64_C(0));
  auto [_x1, front3] = std::move(result3);
  bool c3 = !(front3);
  std::pair<uint64_t,
            std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>>>
      findResult = sl.bde_find(nat_lt, nat_eq, UINT64_C(5));
  auto [status1, _x2] = std::move(findResult);
  bool c4 = status1 == SkipList<int, int>::e_SUCCESS;
  std::pair<uint64_t,
            std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>>>
      findResult2 = sl.bde_find(nat_lt, nat_eq, UINT64_C(9));
  auto [status2, _x3] = std::move(findResult2);
  bool c5 = status2 == SkipList<int, int>::e_NOT_FOUND;
  std::pair<
      std::pair<uint64_t,
                std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>>>,
      bool>
      uniqueResult =
          sl.bde_addUnique(nat_lt, nat_eq, UINT64_C(5), 500u, UINT64_C(0));
  auto [p, _x4] = std::move(uniqueResult);
  auto [status3, _x5] = std::move(p);
  bool c6 = status3 == SkipList<int, int>::e_DUPLICATE;
  std::pair<uint64_t,
            std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>>>
      frontResult = sl.bde_front();
  auto [status4, frontItem] = std::move(frontResult);
  bool c7 = status4 == SkipList<int, int>::e_SUCCESS;
  bool c8;
  if (frontItem.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p0 = *frontItem;
    c8 =
        SkipList<int, int>::template key<uint64_t, uint64_t>(p0) == UINT64_C(3);
  } else {
    c8 = false;
  }
  std::pair<uint64_t,
            std::optional<std::shared_ptr<SkipNode<uint64_t, uint64_t>>>>
      backResult = std::move(sl).bde_back();
  auto [status5, backItem] = std::move(backResult);
  bool c9 = status5 == SkipList<int, int>::e_SUCCESS;
  bool c10;
  if (backItem.has_value()) {
    const std::shared_ptr<SkipNode<uint64_t, uint64_t>> &p0 = *backItem;
    c10 =
        SkipList<int, int>::template key<uint64_t, uint64_t>(p0) == UINT64_C(7);
  } else {
    c10 = false;
  }
  return (
      front1 &&
      (front2 && (c3 && (c4 && (c5 && (c6 && (c7 && (c8 && (c9 && c10)))))))));
}

bool skiplist_test::test_insert_lookup() {
  return stm::atomically([&] { return stm_test_insert_lookup(); });
}

bool skiplist_test::test_delete() {
  return stm::atomically([&] { return stm_test_delete(); });
}

bool skiplist_test::test_update() {
  return stm::atomically([&] { return stm_test_update(); });
}

bool skiplist_test::test_minimum() {
  return stm::atomically([&] { return stm_test_minimum(); });
}

bool skiplist_test::test_length_isEmpty() {
  return stm::atomically([&] { return stm_test_length_isEmpty(); });
}

bool skiplist_test::test_front_back() {
  return stm::atomically([&] { return stm_test_front_back(); });
}

bool skiplist_test::test_popFront() {
  return stm::atomically([&] { return stm_test_popFront(); });
}

bool skiplist_test::test_addUnique() {
  return stm::atomically([&] { return stm_test_addUnique(); });
}

bool skiplist_test::test_find() {
  return stm::atomically([&] { return stm_test_find(); });
}

bool skiplist_test::test_navigation() {
  return stm::atomically([&] { return stm_test_navigation(); });
}

bool skiplist_test::test_bounds() {
  return stm::atomically([&] { return stm_test_bounds(); });
}

bool skiplist_test::test_removeAll() {
  return stm::atomically([&] { return stm_test_removeAll(); });
}

bool skiplist_test::test_bde_api() {
  return stm::atomically([&] { return stm_test_bde_api(); });
}

uint64_t skiplist_test::run_tests() {
  bool r1 = test_insert_lookup();
  bool r2 = test_delete();
  bool r3 = test_update();
  bool r4 = test_minimum();
  bool r5 = test_length_isEmpty();
  bool r6 = test_front_back();
  bool r7 = test_popFront();
  bool r8 = test_addUnique();
  bool r9 = test_find();
  bool r10 = test_navigation();
  bool r11 = test_bounds();
  bool r12 = test_removeAll();
  bool r13 = test_bde_api();
  uint64_t passed = (((((((((((((r1 ? UINT64_C(1) : UINT64_C(0)) +
                                (r2 ? UINT64_C(1) : UINT64_C(0))) +
                               (r3 ? UINT64_C(1) : UINT64_C(0))) +
                              (r4 ? UINT64_C(1) : UINT64_C(0))) +
                             (r5 ? UINT64_C(1) : UINT64_C(0))) +
                            (r6 ? UINT64_C(1) : UINT64_C(0))) +
                           (r7 ? UINT64_C(1) : UINT64_C(0))) +
                          (r8 ? UINT64_C(1) : UINT64_C(0))) +
                         (r9 ? UINT64_C(1) : UINT64_C(0))) +
                        (r10 ? UINT64_C(1) : UINT64_C(0))) +
                       (r11 ? UINT64_C(1) : UINT64_C(0))) +
                      (r12 ? UINT64_C(1) : UINT64_C(0))) +
                     (r13 ? UINT64_C(1) : UINT64_C(0)));
  return passed;
}
