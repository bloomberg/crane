#include <skiplist.h>

bool skiplist_test::nat_lt(const unsigned int &_x0, const unsigned int &_x1) {
  return _x0 < _x1;
}

bool skiplist_test::nat_eq(const unsigned int &_x0, const unsigned int &_x1) {
  return _x0 == _x1;
}

bool skiplist_test::stm_test_insert_lookup() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 2u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 1u);
  sl.insert(nat_lt, nat_eq, 7u, 70u, 0u);
  sl.insert(nat_lt, nat_eq, 1u, 10u, 1u);
  std::optional<unsigned int> v5 = sl.lookup(nat_lt, nat_eq, 5u);
  std::optional<unsigned int> v3 = sl.lookup(nat_lt, nat_eq, 3u);
  std::optional<unsigned int> v7 = sl.lookup(nat_lt, nat_eq, 7u);
  std::optional<unsigned int> v1 = sl.lookup(nat_lt, nat_eq, 1u);
  std::optional<unsigned int> v9 = sl.lookup(nat_lt, nat_eq, 9u);
  bool c1;
  if (v5.has_value()) {
    const unsigned int &n = *v5;
    c1 = n == 50u;
  } else {
    c1 = false;
  }
  bool c2;
  if (v3.has_value()) {
    const unsigned int &n = *v3;
    c2 = n == 30u;
  } else {
    c2 = false;
  }
  bool c3;
  if (v7.has_value()) {
    const unsigned int &n = *v7;
    c3 = n == 70u;
  } else {
    c3 = false;
  }
  bool c4;
  if (v1.has_value()) {
    const unsigned int &n = *v1;
    c4 = n == 10u;
  } else {
    c4 = false;
  }
  bool c5;
  if (v9.has_value()) {
    const unsigned int &_x3 = *v9;
    c5 = false;
  } else {
    c5 = true;
  }
  return (c1 && (c2 && (c3 && (c4 && c5))));
}

bool skiplist_test::stm_test_delete() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 2u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 1u);
  sl.insert(nat_lt, nat_eq, 7u, 70u, 0u);
  sl.remove(nat_lt, nat_eq, 5u);
  std::optional<unsigned int> v5 = sl.lookup(nat_lt, nat_eq, 5u);
  std::optional<unsigned int> v3 = sl.lookup(nat_lt, nat_eq, 3u);
  std::optional<unsigned int> v7 = sl.lookup(nat_lt, nat_eq, 7u);
  bool c1;
  if (v5.has_value()) {
    const unsigned int &_x3 = *v5;
    c1 = false;
  } else {
    c1 = true;
  }
  bool c2;
  if (v3.has_value()) {
    const unsigned int &n = *v3;
    c2 = n == 30u;
  } else {
    c2 = false;
  }
  bool c3;
  if (v7.has_value()) {
    const unsigned int &n = *v7;
    c3 = n == 70u;
  } else {
    c3 = false;
  }
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_update() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 500u, 0u);
  std::optional<unsigned int> v = sl.lookup(nat_lt, nat_eq, 5u);
  return [=]() mutable -> bool {
    if (v.has_value()) {
      const unsigned int &n = *v;
      return n == 500u;
    } else {
      return false;
    }
  }();
}

bool skiplist_test::stm_test_minimum() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 0u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 0u);
  sl.insert(nat_lt, nat_eq, 7u, 70u, 0u);
  std::optional<std::pair<unsigned int, unsigned int>> minOpt = sl.minimum();
  return [=]() mutable -> bool {
    if (minOpt.has_value()) {
      const std::pair<unsigned int, unsigned int> &p = *minOpt;
      const unsigned int &k = p.first;
      const unsigned int &v = p.second;
      return (k == 3u && v == 30u);
    } else {
      return false;
    }
  }();
}

bool skiplist_test::stm_test_length_isEmpty() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  bool empty1 = sl.isEmpty();
  unsigned int len1 = sl.length();
  sl.insert(nat_lt, nat_eq, 5u, 50u, 0u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 0u);
  bool empty2 = sl.isEmpty();
  unsigned int len2 = sl.length();
  bool c2 = len1 == 0u;
  bool c3 = !(empty2);
  bool c4 = len2 == 2u;
  return (empty1 && (c2 && (c3 && c4)));
}

bool skiplist_test::stm_test_front_back() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 0u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 0u);
  sl.insert(nat_lt, nat_eq, 7u, 70u, 0u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      frontOpt = sl.front();
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> backOpt =
      sl.back();
  bool c1;
  if (frontOpt.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p = *frontOpt;
    c1 = SkipList<int, int>::template key<unsigned int, unsigned int>(p) == 3u;
  } else {
    c1 = false;
  }
  bool c2;
  if (backOpt.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p = *backOpt;
    c2 = SkipList<int, int>::template key<unsigned int, unsigned int>(p) == 7u;
  } else {
    c2 = false;
  }
  return (c1 && c2);
}

bool skiplist_test::stm_test_popFront() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 0u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 0u);
  sl.insert(nat_lt, nat_eq, 7u, 70u, 0u);
  std::optional<std::pair<unsigned int, unsigned int>> pop1 = sl.popFront();
  std::optional<std::pair<unsigned int, unsigned int>> pop2 = sl.popFront();
  unsigned int len = sl.length();
  bool c1;
  if (pop1.has_value()) {
    const std::pair<unsigned int, unsigned int> &p = *pop1;
    const unsigned int &k = p.first;
    const unsigned int &v = p.second;
    c1 = (k == 3u && v == 30u);
  } else {
    c1 = false;
  }
  bool c2;
  if (pop2.has_value()) {
    const std::pair<unsigned int, unsigned int> &p = *pop2;
    const unsigned int &k = p.first;
    const unsigned int &v = p.second;
    c2 = (k == 5u && v == 50u);
  } else {
    c2 = false;
  }
  bool c3 = len == 1u;
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_addUnique() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  bool r1 = sl.addUnique(nat_lt, nat_eq, 5u, 50u, 0u);
  bool r2 = sl.addUnique(nat_lt, nat_eq, 5u, 500u, 0u);
  bool r3 = sl.addUnique(nat_lt, nat_eq, 3u, 30u, 0u);
  std::optional<unsigned int> v5 = sl.lookup(nat_lt, nat_eq, 5u);
  unsigned int len = sl.length();
  bool c2 = !(r2);
  bool c4;
  if (v5.has_value()) {
    const unsigned int &n = *v5;
    c4 = n == 50u;
  } else {
    c4 = false;
  }
  bool c5 = len == 2u;
  return (r1 && (c2 && (r3 && (c4 && c5))));
}

bool skiplist_test::stm_test_find() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 0u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 0u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> pairOpt =
      sl.find(nat_lt, nat_eq, 5u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> noneOpt =
      sl.find(nat_lt, nat_eq, 9u);
  bool c1;
  if (pairOpt.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p = *pairOpt;
    unsigned int k =
        SkipList<int, int>::template key<unsigned int, unsigned int>(p);
    c1 = k == 5u;
  } else {
    c1 = false;
  }
  bool c2;
  if (noneOpt.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &_x1 = *noneOpt;
    c2 = false;
  } else {
    c2 = true;
  }
  return (c1 && c2);
}

bool skiplist_test::stm_test_navigation() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 1u, 10u, 0u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 0u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      frontOpt = sl.front();
  if (frontOpt.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &first =
        *frontOpt;
    std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
        nextOpt = SkipList<int, int>::template next<unsigned int, unsigned int>(
            first);
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &second =
          *nextOpt;
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
          prevOpt = std::move(sl).previous(nat_eq, second);
      bool c1 = SkipList<int, int>::template key<unsigned int, unsigned int>(
                    first) == 1u;
      bool c2 = SkipList<int, int>::template key<unsigned int, unsigned int>(
                    second) == 3u;
      bool c3;
      if (prevOpt.has_value()) {
        const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p =
            *prevOpt;
        c3 = SkipList<int, int>::template key<unsigned int, unsigned int>(p) ==
             1u;
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
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 2u, 20u, 0u);
  sl.insert(nat_lt, nat_eq, 4u, 40u, 0u);
  sl.insert(nat_lt, nat_eq, 6u, 60u, 0u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> lb3 =
      sl.findLowerBound(nat_lt, 3u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> lb4 =
      sl.findLowerBound(nat_lt, 4u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> ub4 =
      sl.findUpperBound(nat_lt, nat_eq, 4u);
  bool c1;
  if (lb3.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p = *lb3;
    c1 = SkipList<int, int>::template key<unsigned int, unsigned int>(p) == 4u;
  } else {
    c1 = false;
  }
  bool c2;
  if (lb4.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p = *lb4;
    c2 = SkipList<int, int>::template key<unsigned int, unsigned int>(p) == 4u;
  } else {
    c2 = false;
  }
  bool c3;
  if (ub4.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p = *ub4;
    c3 = SkipList<int, int>::template key<unsigned int, unsigned int>(p) == 6u;
  } else {
    c3 = false;
  }
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_removeAll() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  sl.insert(nat_lt, nat_eq, 5u, 50u, 0u);
  sl.insert(nat_lt, nat_eq, 3u, 30u, 0u);
  sl.insert(nat_lt, nat_eq, 7u, 70u, 0u);
  unsigned int count = sl.removeAll();
  bool empty = sl.isEmpty();
  unsigned int len = sl.length();
  bool c1 = count == 3u;
  bool c3 = len == 0u;
  return (c1 && (empty && c3));
}

bool skiplist_test::stm_test_bde_api() {
  SkipList<unsigned int, unsigned int> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0u, 0u);
  std::pair<std::shared_ptr<SkipNode<unsigned int, unsigned int>>, bool>
      result1 = sl.bde_add(nat_lt, nat_eq, 5u, 50u, 0u);
  const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &_x =
      result1.first;
  const bool &front1 = result1.second;
  std::pair<std::shared_ptr<SkipNode<unsigned int, unsigned int>>, bool>
      result2 = sl.bde_add(nat_lt, nat_eq, 3u, 30u, 0u);
  const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &_x0 =
      result2.first;
  const bool &front2 = result2.second;
  std::pair<std::shared_ptr<SkipNode<unsigned int, unsigned int>>, bool>
      result3 = sl.bde_add(nat_lt, nat_eq, 7u, 70u, 0u);
  const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &_x1 =
      result3.first;
  const bool &front3 = result3.second;
  bool c3 = !(front3);
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      findResult = sl.bde_find(nat_lt, nat_eq, 5u);
  const unsigned int &status1 = findResult.first;
  const std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      &_x2 = findResult.second;
  bool c4 = status1 == SkipList<int, int>::e_SUCCESS;
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      findResult2 = sl.bde_find(nat_lt, nat_eq, 9u);
  const unsigned int &status2 = findResult2.first;
  const std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      &_x3 = findResult2.second;
  bool c5 = status2 == SkipList<int, int>::e_NOT_FOUND;
  std::pair<std::pair<unsigned int, std::optional<std::shared_ptr<
                                        SkipNode<unsigned int, unsigned int>>>>,
            bool>
      uniqueResult = sl.bde_addUnique(nat_lt, nat_eq, 5u, 500u, 0u);
  const std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>> &p =
      uniqueResult.first;
  const bool &_x4 = uniqueResult.second;
  const unsigned int &status3 = p.first;
  const std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      &_x5 = p.second;
  bool c6 = status3 == SkipList<int, int>::e_DUPLICATE;
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      frontResult = sl.bde_front();
  const unsigned int &status4 = frontResult.first;
  const std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      &frontItem = frontResult.second;
  bool c7 = status4 == SkipList<int, int>::e_SUCCESS;
  bool c8;
  if (frontItem.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p0 =
        *frontItem;
    c8 = SkipList<int, int>::template key<unsigned int, unsigned int>(p0) == 3u;
  } else {
    c8 = false;
  }
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      backResult = std::move(sl).bde_back();
  const unsigned int &status5 = backResult.first;
  const std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      &backItem = backResult.second;
  bool c9 = status5 == SkipList<int, int>::e_SUCCESS;
  bool c10;
  if (backItem.has_value()) {
    const std::shared_ptr<SkipNode<unsigned int, unsigned int>> &p0 = *backItem;
    c10 =
        SkipList<int, int>::template key<unsigned int, unsigned int>(p0) == 7u;
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

unsigned int skiplist_test::run_tests() {
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
  unsigned int passed =
      (((((((((((((r1 ? 1u : 0u) + (r2 ? 1u : 0u)) + (r3 ? 1u : 0u)) +
                (r4 ? 1u : 0u)) +
               (r5 ? 1u : 0u)) +
              (r6 ? 1u : 0u)) +
             (r7 ? 1u : 0u)) +
            (r8 ? 1u : 0u)) +
           (r9 ? 1u : 0u)) +
          (r10 ? 1u : 0u)) +
         (r11 ? 1u : 0u)) +
        (r12 ? 1u : 0u)) +
       (r13 ? 1u : 0u));
  return passed;
}
