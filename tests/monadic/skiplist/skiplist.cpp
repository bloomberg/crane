#include <algorithm>
#include <any>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <skiplist.h>
#include <skipnode.h>
#include <string>
#include <utility>
#include <variant>
#include <vector>

bool Nat::eqb(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      unsigned int _x = m - 1;
      return false;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return eqb(n_, m_);
    }
  }
}

bool Nat::leb(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return leb(n_, m_);
    }
  }
}

bool Nat::ltb(const unsigned int n, const unsigned int m) {
  return leb((n + 1), m);
}

bool skiplist_test::nat_lt(const unsigned int _x0, const unsigned int _x1) {
  return Nat::ltb(_x0, _x1);
}

bool skiplist_test::nat_eq(const unsigned int _x0, const unsigned int _x1) {
  return Nat::eqb(_x0, _x1);
}

bool skiplist_test::stm_test_insert_lookup() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 2u);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 1u);
  sl->insert(nat_lt, nat_eq, 7u, 70u, 0);
  sl->insert(nat_lt, nat_eq, 1u, 10u, 1u);
  std::optional<unsigned int> v5 = sl->lookup(nat_lt, nat_eq, 5u);
  std::optional<unsigned int> v3 = sl->lookup(nat_lt, nat_eq, 3u);
  std::optional<unsigned int> v7 = sl->lookup(nat_lt, nat_eq, 7u);
  std::optional<unsigned int> v1 = sl->lookup(nat_lt, nat_eq, 1u);
  std::optional<unsigned int> v9 = sl->lookup(nat_lt, nat_eq, 9u);
  bool c1;
  if (v5.has_value()) {
    unsigned int n = *v5;
    c1 = Nat::eqb(n, 50u);
  } else {
    c1 = false;
  }
  bool c2;
  if (v3.has_value()) {
    unsigned int n = *v3;
    c2 = Nat::eqb(n, 30u);
  } else {
    c2 = false;
  }
  bool c3;
  if (v7.has_value()) {
    unsigned int n = *v7;
    c3 = Nat::eqb(n, 70u);
  } else {
    c3 = false;
  }
  bool c4;
  if (v1.has_value()) {
    unsigned int n = *v1;
    c4 = Nat::eqb(n, 10u);
  } else {
    c4 = false;
  }
  bool c5;
  if (v9.has_value()) {
    unsigned int _x4 = *v9;
    c5 = false;
  } else {
    c5 = true;
  }
  return (c1 && (c2 && (c3 && (c4 && c5))));
}

bool skiplist_test::stm_test_delete() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 2u);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 1u);
  sl->insert(nat_lt, nat_eq, 7u, 70u, 0);
  sl->remove(nat_lt, nat_eq, 5u);
  std::optional<unsigned int> v5 = sl->lookup(nat_lt, nat_eq, 5u);
  std::optional<unsigned int> v3 = sl->lookup(nat_lt, nat_eq, 3u);
  std::optional<unsigned int> v7 = sl->lookup(nat_lt, nat_eq, 7u);
  bool c1;
  if (v5.has_value()) {
    unsigned int _x4 = *v5;
    c1 = false;
  } else {
    c1 = true;
  }
  bool c2;
  if (v3.has_value()) {
    unsigned int n = *v3;
    c2 = Nat::eqb(n, 30u);
  } else {
    c2 = false;
  }
  bool c3;
  if (v7.has_value()) {
    unsigned int n = *v7;
    c3 = Nat::eqb(n, 70u);
  } else {
    c3 = false;
  }
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_update() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 0);
  sl->insert(nat_lt, nat_eq, 5u, 500u, 0);
  std::optional<unsigned int> v = sl->lookup(nat_lt, nat_eq, 5u);
  return [&](void) {
    if (v.has_value()) {
      unsigned int n = *v;
      return Nat::eqb(n, 500u);
    } else {
      return false;
    }
  }();
}

bool skiplist_test::stm_test_minimum() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 0);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 0);
  sl->insert(nat_lt, nat_eq, 7u, 70u, 0);
  std::optional<std::pair<unsigned int, unsigned int>> minOpt = sl->minimum();
  return [&](void) {
    if (minOpt.has_value()) {
      std::pair<unsigned int, unsigned int> p = *minOpt;
      unsigned int k = p.first;
      unsigned int v = p.second;
      return (Nat::eqb(k, 3u) && Nat::eqb(v, 30u));
    } else {
      return false;
    }
  }();
}

bool skiplist_test::stm_test_length_isEmpty() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  bool empty1 = sl->isEmpty();
  unsigned int len1 = sl->length();
  sl->insert(nat_lt, nat_eq, 5u, 50u, 0);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 0);
  bool empty2 = sl->isEmpty();
  unsigned int len2 = sl->length();
  bool c2 = Nat::eqb(len1, 0);
  bool c3 = !(empty2);
  bool c4 = Nat::eqb(len2, 2u);
  return (empty1 && (c2 && (c3 && c4)));
}

bool skiplist_test::stm_test_front_back() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 0);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 0);
  sl->insert(nat_lt, nat_eq, 7u, 70u, 0);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      frontOpt = sl->front();
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> backOpt =
      sl->back();
  bool c1;
  if (frontOpt.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> p = *frontOpt;
    c1 = Nat::eqb(
        SkipList<int, int>::template key<unsigned int, unsigned int>(p),
        (((0 + 1) + 1) + 1));
  } else {
    c1 = false;
  }
  bool c2;
  if (backOpt.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> p = *backOpt;
    c2 = Nat::eqb(
        SkipList<int, int>::template key<unsigned int, unsigned int>(p),
        (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else {
    c2 = false;
  }
  return (c1 && c2);
}

bool skiplist_test::stm_test_popFront() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 0);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 0);
  sl->insert(nat_lt, nat_eq, 7u, 70u, 0);
  std::optional<std::pair<unsigned int, unsigned int>> pop1 = sl->popFront();
  std::optional<std::pair<unsigned int, unsigned int>> pop2 = sl->popFront();
  unsigned int len = sl->length();
  bool c1;
  if (pop1.has_value()) {
    std::pair<unsigned int, unsigned int> p = *pop1;
    unsigned int k = p.first;
    unsigned int v = p.second;
    c1 = (Nat::eqb(k, 3u) && Nat::eqb(v, 30u));
  } else {
    c1 = false;
  }
  bool c2;
  if (pop2.has_value()) {
    std::pair<unsigned int, unsigned int> p = *pop2;
    unsigned int k = p.first;
    unsigned int v = p.second;
    c2 = (Nat::eqb(k, 5u) && Nat::eqb(v, 50u));
  } else {
    c2 = false;
  }
  bool c3 = Nat::eqb(len, 1u);
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_addUnique() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  bool r1 = sl->addUnique(nat_lt, nat_eq, 5u, 50u, 0);
  bool r2 = sl->addUnique(nat_lt, nat_eq, 5u, 500u, 0);
  bool r3 = sl->addUnique(nat_lt, nat_eq, 3u, 30u, 0);
  std::optional<unsigned int> v5 = sl->lookup(nat_lt, nat_eq, 5u);
  unsigned int len = sl->length();
  bool c2 = !(r2);
  bool c4;
  if (v5.has_value()) {
    unsigned int n = *v5;
    c4 = Nat::eqb(n, 50u);
  } else {
    c4 = false;
  }
  bool c5 = Nat::eqb(len, 2u);
  return (r1 && (c2 && (r3 && (c4 && c5))));
}

bool skiplist_test::stm_test_find() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 0);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 0);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> pairOpt =
      sl->find(nat_lt, nat_eq, 5u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> noneOpt =
      sl->find(nat_lt, nat_eq, 9u);
  bool c1;
  if (pairOpt.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> p = *pairOpt;
    unsigned int k =
        SkipList<int, int>::template key<unsigned int, unsigned int>(p);
    c1 = Nat::eqb(k, 5u);
  } else {
    c1 = false;
  }
  bool c2;
  if (noneOpt.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> _x2 = *noneOpt;
    c2 = false;
  } else {
    c2 = true;
  }
  return (c1 && c2);
}

bool skiplist_test::stm_test_navigation() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 1u, 10u, 0);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 0);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      frontOpt = sl->front();
  if (frontOpt.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> first = *frontOpt;
    std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
        nextOpt = SkipList<int, int>::template next<unsigned int, unsigned int>(
            first);
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<unsigned int, unsigned int>> second = *nextOpt;
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
          prevOpt = sl->previous(nat_eq, second);
      bool c1 = Nat::eqb(
          SkipList<int, int>::template key<unsigned int, unsigned int>(first),
          1u);
      bool c2 = Nat::eqb(
          SkipList<int, int>::template key<unsigned int, unsigned int>(second),
          3u);
      bool c3;
      if (prevOpt.has_value()) {
        std::shared_ptr<SkipNode<unsigned int, unsigned int>> p = *prevOpt;
        c3 = Nat::eqb(
            SkipList<int, int>::template key<unsigned int, unsigned int>(p),
            1u);
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
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 2u, 20u, 0);
  sl->insert(nat_lt, nat_eq, 4u, 40u, 0);
  sl->insert(nat_lt, nat_eq, 6u, 60u, 0);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> lb3 =
      sl->findLowerBound(nat_lt, 3u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> lb4 =
      sl->findLowerBound(nat_lt, 4u);
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> ub4 =
      sl->findUpperBound(nat_lt, nat_eq, 4u);
  bool c1;
  if (lb3.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> p = *lb3;
    c1 = Nat::eqb(
        SkipList<int, int>::template key<unsigned int, unsigned int>(p), 4u);
  } else {
    c1 = false;
  }
  bool c2;
  if (lb4.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> p = *lb4;
    c2 = Nat::eqb(
        SkipList<int, int>::template key<unsigned int, unsigned int>(p), 4u);
  } else {
    c2 = false;
  }
  bool c3;
  if (ub4.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> p = *ub4;
    c3 = Nat::eqb(
        SkipList<int, int>::template key<unsigned int, unsigned int>(p), 6u);
  } else {
    c3 = false;
  }
  return (c1 && (c2 && c3));
}

bool skiplist_test::stm_test_removeAll() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  sl->insert(nat_lt, nat_eq, 5u, 50u, 0);
  sl->insert(nat_lt, nat_eq, 3u, 30u, 0);
  sl->insert(nat_lt, nat_eq, 7u, 70u, 0);
  unsigned int count = sl->removeAll();
  bool empty = sl->isEmpty();
  unsigned int len = sl->length();
  bool c1 = Nat::eqb(count, 3u);
  bool c3 = Nat::eqb(len, 0);
  return (c1 && (empty && c3));
}

bool skiplist_test::stm_test_bde_api() {
  std::shared_ptr<SkipList<unsigned int, unsigned int>> sl =
      SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
  std::pair<std::shared_ptr<SkipNode<unsigned int, unsigned int>>, bool>
      result1 = sl->bde_add(nat_lt, nat_eq, 5u, 50u, 0);
  std::shared_ptr<SkipNode<unsigned int, unsigned int>> _x0 = result1.first;
  bool front1 = result1.second;
  std::pair<std::shared_ptr<SkipNode<unsigned int, unsigned int>>, bool>
      result2 = sl->bde_add(nat_lt, nat_eq, 3u, 30u, 0);
  std::shared_ptr<SkipNode<unsigned int, unsigned int>> _x1 = result2.first;
  bool front2 = result2.second;
  std::pair<std::shared_ptr<SkipNode<unsigned int, unsigned int>>, bool>
      result3 = sl->bde_add(nat_lt, nat_eq, 7u, 70u, 0);
  std::shared_ptr<SkipNode<unsigned int, unsigned int>> _x2 = result3.first;
  bool front3 = result3.second;
  bool c3 = !(front3);
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      findResult = sl->bde_find(nat_lt, nat_eq, 5u);
  unsigned int status1 = findResult.first;
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> _x3 =
      findResult.second;
  bool c4 = Nat::eqb(status1, SkipList<int, int>::e_SUCCESS);
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      findResult2 = sl->bde_find(nat_lt, nat_eq, 9u);
  unsigned int status2 = findResult2.first;
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> _x4 =
      findResult2.second;
  bool c5 = Nat::eqb(status2, SkipList<int, int>::e_NOT_FOUND);
  std::pair<std::pair<unsigned int, std::optional<std::shared_ptr<
                                        SkipNode<unsigned int, unsigned int>>>>,
            bool>
      uniqueResult = sl->bde_addUnique(nat_lt, nat_eq, 5u, 500u, 0);
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      p = uniqueResult.first;
  bool _x5 = uniqueResult.second;
  unsigned int status3 = p.first;
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>> _x6 =
      p.second;
  bool c6 = Nat::eqb(status3, SkipList<int, int>::e_DUPLICATE);
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      frontResult = sl->bde_front();
  unsigned int status4 = frontResult.first;
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      frontItem = frontResult.second;
  bool c7 = Nat::eqb(status4, SkipList<int, int>::e_SUCCESS);
  bool c8;
  if (frontItem.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> p0 = *frontItem;
    c8 = Nat::eqb(
        SkipList<int, int>::template key<unsigned int, unsigned int>(p0), 3u);
  } else {
    c8 = false;
  }
  std::pair<
      unsigned int,
      std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>>
      backResult = sl->bde_back();
  unsigned int status5 = backResult.first;
  std::optional<std::shared_ptr<SkipNode<unsigned int, unsigned int>>>
      backItem = backResult.second;
  bool c9 = Nat::eqb(status5, SkipList<int, int>::e_SUCCESS);
  bool c10;
  if (backItem.has_value()) {
    std::shared_ptr<SkipNode<unsigned int, unsigned int>> p0 = *backItem;
    c10 = Nat::eqb(
        SkipList<int, int>::template key<unsigned int, unsigned int>(p0), 7u);
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
  unsigned int passed = (((((((((((([&](void) {
                                     if (r1) {
                                       return 1u;
                                     } else {
                                       return 0u;
                                     }
                                   }() +
                                    [&](void) {
                                      if (r2) {
                                        return 1u;
                                      } else {
                                        return 0u;
                                      }
                                    }()) +
                                   [&](void) {
                                     if (r3) {
                                       return 1u;
                                     } else {
                                       return 0u;
                                     }
                                   }()) +
                                  [&](void) {
                                    if (r4) {
                                      return 1u;
                                    } else {
                                      return 0u;
                                    }
                                  }()) +
                                 [&](void) {
                                   if (r5) {
                                     return 1u;
                                   } else {
                                     return 0u;
                                   }
                                 }()) +
                                [&](void) {
                                  if (r6) {
                                    return 1u;
                                  } else {
                                    return 0u;
                                  }
                                }()) +
                               [&](void) {
                                 if (r7) {
                                   return 1u;
                                 } else {
                                   return 0u;
                                 }
                               }()) +
                              [&](void) {
                                if (r8) {
                                  return 1u;
                                } else {
                                  return 0u;
                                }
                              }()) +
                             [&](void) {
                               if (r9) {
                                 return 1u;
                               } else {
                                 return 0u;
                               }
                             }()) +
                            [&](void) {
                              if (r10) {
                                return 1u;
                              } else {
                                return 0u;
                              }
                            }()) +
                           [&](void) {
                             if (r11) {
                               return 1u;
                             } else {
                               return 0u;
                             }
                           }()) +
                          [&](void) {
                            if (r12) {
                              return 1u;
                            } else {
                              return 0u;
                            }
                          }()) +
                         [&](void) {
                           if (r13) {
                             return 1u;
                           } else {
                             return 0u;
                           }
                         }());
  return passed;
}
