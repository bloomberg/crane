#ifndef INCLUDED_SKIPLIST
#define INCLUDED_SKIPLIST

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <skipnode.h>
#include <stm_adapter.h>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>

struct SkipList_Mod {
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static std::shared_ptr<SkipNode<T1, T2>>
  findPred_go(F0 &&ltK, uint64_t fuel, std::shared_ptr<SkipNode<T1, T2>> curr,
              const T1 &target, uint64_t level) {
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = std::move(curr);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return _loop_curr;
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[level]));
        if (nextOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &next0 = *nextOpt;
          if (ltK(next0->key, target)) {
            _loop_curr = next0;
            _loop_fuel = fuel_;
          } else {
            return _loop_curr;
          }
        } else {
          return _loop_curr;
        }
      }
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static std::shared_ptr<SkipNode<T1, T2>>
  findPred(F0 &&ltK, std::shared_ptr<SkipNode<T1, T2>> curr, const T1 &target,
           uint64_t level) {
    return findPred_go<T1, T2>(ltK, 10000u, curr, target, level);
  }

  template <typename K, typename V> struct SkipList {
    std::shared_ptr<SkipNode<K, V>> slHead;
    uint64_t slMaxLevel;
    stm::TVar<uint64_t> slLevel;
    stm::TVar<uint64_t> slLength;
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static SkipPath<T1, T2>
  findPath_aux(F0 &&ltK, std::shared_ptr<SkipNode<T1, T2>> curr,
               const T1 &target, uint64_t level, SkipPath<T1, T2> path) {
    uint64_t _loop_level = std::move(level);
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = std::move(curr);
    while (true) {
      std::shared_ptr<SkipNode<T1, T2>> pred =
          findPred<T1, T2>(ltK, _loop_curr, target, _loop_level);
      path.set(_loop_level, pred);
      if (_loop_level <= 0) {
        return path;
      } else {
        uint64_t level_ = _loop_level - 1;
        _loop_level = level_;
        _loop_curr = std::move(pred);
      }
    }
  }

  template <typename T1, typename T2>
  static void linkAtLevel(std::shared_ptr<SkipNode<T1, T2>> pred,
                          std::shared_ptr<SkipNode<T1, T2>> newNode,
                          uint64_t level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> oldNext = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(pred->forward[level]));
    stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level],
        opt_to_ptr(
            std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(newNode)));
    stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
        std::move(newNode)->forward[level], opt_to_ptr(std::move(oldNext)));
    return;
  }

  template <typename T1, typename T2>
  static void
  linkNode_aux(SkipPath<T1, T2> path, std::shared_ptr<SkipNode<T1, T2>>,
               std::shared_ptr<SkipNode<T1, T2>> newNode, uint64_t level) {
    uint64_t _loop_level = std::move(level);
    while (true) {
      std::shared_ptr<SkipNode<T1, T2>> pred = path.get(_loop_level);
      linkAtLevel<T1, T2>(pred, newNode, _loop_level);
      if (_loop_level <= 0) {
        return;
      } else {
        uint64_t level_ = _loop_level - 1;
        _loop_level = level_;
      }
    }
    return;
  }

  template <typename T1, typename T2>
  static void extendPath_aux(SkipPath<T1, T2> path,
                             std::shared_ptr<SkipNode<T1, T2>> head,
                             uint64_t level, uint64_t maxLevel) {
    uint64_t _loop_level = std::move(level);
    while (true) {
      if (_loop_level <= 0) {
        path.set(UINT64_C(0), head);
        return;
      } else {
        uint64_t level_ = _loop_level - 1;
        path.set(_loop_level, head);
        if (maxLevel <= level_) {
          _loop_level = level_;
        } else {
          return;
        }
      }
    }
    return;
  }

  template <typename T1, typename T2>
  static void extendPath(SkipPath<T1, T2> path,
                         std::shared_ptr<SkipNode<T1, T2>> head,
                         uint64_t needed, uint64_t currentMax) {
    if (needed <= (currentMax + 1)) {
      return;
    } else {
      extendPath_aux<T1, T2>(
          path, head,
          (((needed - UINT64_C(1)) > needed ? 0 : (needed - UINT64_C(1)))),
          (currentMax + UINT64_C(1)));
      return;
    }
  }

  template <typename T1, typename T2>
  static void linkNode(SkipPath<T1, T2> path,
                       std::shared_ptr<SkipNode<T1, T2>> head,
                       std::shared_ptr<SkipNode<T1, T2>> newNode) {
    uint64_t lvl = newNode->level;
    linkNode_aux<T1, T2>(path, head, newNode, lvl);
    return;
  }

  template <typename T1, typename T2>
  static void unlinkAtLevel(std::shared_ptr<SkipNode<T1, T2>> pred,
                            std::shared_ptr<SkipNode<T1, T2>> target,
                            uint64_t level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> targetNext =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
            target->forward[level]));
    stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level], opt_to_ptr(std::move(targetNext)));
    return;
  }

  template <typename T1, typename T2>
  static void unlinkNode_aux(SkipPath<T1, T2> path,
                             std::shared_ptr<SkipNode<T1, T2>> target,
                             uint64_t level) {
    uint64_t _loop_level = std::move(level);
    while (true) {
      std::shared_ptr<SkipNode<T1, T2>> pred = path.get(_loop_level);
      unlinkAtLevel<T1, T2>(pred, target, _loop_level);
      if (_loop_level <= 0) {
        return;
      } else {
        uint64_t level_ = _loop_level - 1;
        _loop_level = level_;
      }
    }
    return;
  }

  template <typename T1, typename T2>
  static void unlinkNode(SkipPath<T1, T2> path,
                         std::shared_ptr<SkipNode<T1, T2>> target) {
    uint64_t lvl = target->level;
    unlinkNode_aux<T1, T2>(path, target, lvl);
    return;
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bool findKey_aux(F0 &&ltK, F1 &&eqK,
                          std::shared_ptr<SkipNode<T1, T2>> curr,
                          const T1 &target, uint64_t level) {
    uint64_t _loop_level = std::move(level);
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = std::move(curr);
    while (true) {
      std::shared_ptr<SkipNode<T1, T2>> pred =
          findPred<T1, T2>(ltK, _loop_curr, target, _loop_level);
      if (_loop_level <= 0) {
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                std::move(pred)->forward[UINT64_C(0)]));
        if (nextOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &node = *nextOpt;
          return eqK(node->key, target);
        } else {
          return false;
        }
      } else {
        uint64_t level_ = _loop_level - 1;
        _loop_level = level_;
        _loop_curr = std::move(pred);
      }
    }
  }

  template <typename T1, typename T2>
  static uint64_t
  length_aux(uint64_t fuel,
             const std::optional<std::shared_ptr<SkipNode<T1, T2>>> &node,
             uint64_t acc) {
    uint64_t _loop_acc = std::move(acc);
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> _loop_node = node;
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return _loop_acc;
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        if (_loop_node.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &n = *_loop_node;
          std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
              ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                  n->forward[UINT64_C(0)]));
          _loop_acc = (_loop_acc + 1);
          _loop_node = std::move(nextOpt);
          _loop_fuel = fuel_;
        } else {
          return _loop_acc;
        }
      }
    }
  }

  template <typename T1, typename T2>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findLast_aux(uint64_t fuel, std::shared_ptr<SkipNode<T1, T2>> curr) {
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = std::move(curr);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(
            _loop_curr);
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[UINT64_C(0)]));
        if (nextOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &next0 = *nextOpt;
          _loop_curr = next0;
          _loop_fuel = fuel_;
        } else {
          return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(
              std::move(_loop_curr));
        }
      }
    }
  }

  template <typename T1, typename T2>
  static void unlinkFirstFromHead(std::shared_ptr<SkipNode<T1, T2>> head,
                                  std::shared_ptr<SkipNode<T1, T2>> node,
                                  uint64_t lvl) {
    uint64_t _loop_lvl = std::move(lvl);
    while (true) {
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
          ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
              node->forward[_loop_lvl]));
      stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
          head->forward[_loop_lvl], opt_to_ptr(nodeNext));
      if (_loop_lvl <= 0) {
        return;
      } else {
        uint64_t lvl_ = _loop_lvl - 1;
        _loop_lvl = lvl_;
      }
    }
    return;
  }

  template <typename T1, typename T2>
  static void unlinkNodeAtAllLevels(std::shared_ptr<SkipNode<T1, T2>> head,
                                    std::shared_ptr<SkipNode<T1, T2>> node,
                                    uint64_t lvl) {
    uint64_t _loop_lvl = std::move(lvl);
    while (true) {
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
          ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
              node->forward[_loop_lvl]));
      stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
          head->forward[_loop_lvl], opt_to_ptr(nodeNext));
      if (_loop_lvl <= 0) {
        return;
      } else {
        uint64_t lvl_ = _loop_lvl - 1;
        _loop_lvl = lvl_;
      }
    }
    return;
  }

  template <typename T1, typename T2>
  static uint64_t removeAll_aux(uint64_t fuel,
                                std::shared_ptr<SkipNode<T1, T2>> head,
                                uint64_t acc) {
    uint64_t _loop_acc = std::move(acc);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return _loop_acc;
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                head->forward[UINT64_C(0)]));
        if (firstOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &node = *firstOpt;
          unlinkNodeAtAllLevels<T1, T2>(head, node, node->level);
          _loop_acc = (_loop_acc + 1);
          _loop_fuel = fuel_;
        } else {
          return _loop_acc;
        }
      }
    }
  }

  template <typename T1, typename T2>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  next(std::shared_ptr<SkipNode<T1, T2>> pair) {
    return ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
        pair->forward[UINT64_C(0)]));
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findPrev_aux(F0 &&eqK, uint64_t fuel, std::shared_ptr<SkipNode<T1, T2>> curr,
               std::shared_ptr<SkipNode<T1, T2>> _x, const T1 &target) {
    std::shared_ptr<SkipNode<T1, T2>> _loop_x = std::move(_x);
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = std::move(curr);
    uint64_t _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return std::optional<std::shared_ptr<SkipNode<T1, T2>>>();
      } else {
        uint64_t fuel_ = _loop_fuel - 1;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[UINT64_C(0)]));
        if (nextOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &next0 = *nextOpt;
          if (eqK(next0->key, target)) {
            return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(
                std::move(_loop_curr));
          } else {
            std::shared_ptr<SkipNode<T1, T2>> _next_curr = next0;
            _loop_x = std::move(_loop_curr);
            _loop_fuel = fuel_;
            _loop_curr = std::move(_next_curr);
          }
        } else {
          return std::optional<std::shared_ptr<SkipNode<T1, T2>>>();
        }
      }
    }
  }

  template <typename T1, typename T2>
  static T1 key(std::shared_ptr<SkipNode<T1, T2>> pair) {
    return pair->key;
  }

  template <typename T1, typename T2>
  static T2 data(std::shared_ptr<SkipNode<T1, T2>> pair) {
    return stm::readTVar<T2>(pair->value);
  }

  static inline const uint64_t e_SUCCESS = UINT64_C(0);
  static inline const uint64_t e_NOT_FOUND = UINT64_C(1);
  static inline const uint64_t e_DUPLICATE = UINT64_C(2);
  static inline const uint64_t e_INVALID = UINT64_C(3);

  template <typename T1, typename T2>
  static std::pair<uint64_t, std::optional<std::shared_ptr<SkipNode<T1, T2>>>>
  bde_next(std::shared_ptr<SkipNode<T1, T2>> pair) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
        next<T1, T2>(pair);
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<T1, T2>> &node = *nextOpt;
      return std::make_pair(
          e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return std::make_pair(e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<T1, T2>>>());
    }
  }

  template <typename T1, typename T2>
  static SkipList<T1, T2> create(const T1 &dummyKey, const T2 &dummyVal) {
    std::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal,
        (((16u - UINT64_C(1)) > 16u ? 0 : (16u - UINT64_C(1)))));
    stm::TVar<uint64_t> lvlTV = stm::newTVar(UINT64_C(0));
    stm::TVar<uint64_t> lenTV = stm::newTVar(UINT64_C(0));
    return SkipList<T1, T2>{headNode, 16u, lvlTV, lenTV};
  }

  template <typename T1, typename T2>
  static SkipList<T1, T2> createIO(const T1 &dummyKey, const T2 &dummyVal) {
    return stm::atomically([&] { return create<T1, T2>(dummyKey, dummyVal); });
  }
};

struct skiplist_test {
  static bool nat_lt(uint64_t _x0, uint64_t _x1);
  static bool nat_eq(uint64_t _x0, uint64_t _x1);
  static bool stm_test_insert_lookup();
  static bool stm_test_delete();
  static bool stm_test_update();
  static bool stm_test_minimum();
  static bool stm_test_length_isEmpty();
  static bool stm_test_front_back();
  static bool stm_test_popFront();
  static bool stm_test_addUnique();
  static bool stm_test_find();
  static bool stm_test_navigation();
  static bool stm_test_bounds();
  static bool stm_test_removeAll();
  static bool stm_test_bde_api();
  static bool test_insert_lookup();
  static bool test_delete();
  static bool test_update();
  static bool test_minimum();
  static bool test_length_isEmpty();
  static bool test_front_back();
  static bool test_popFront();
  static bool test_addUnique();
  static bool test_find();
  static bool test_navigation();
  static bool test_bounds();
  static bool test_removeAll();
  static bool test_bde_api();
  static uint64_t run_tests();
};

#endif // INCLUDED_SKIPLIST
