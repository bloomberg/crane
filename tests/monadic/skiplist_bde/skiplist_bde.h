#ifndef INCLUDED_SKIPLIST_BDE
#define INCLUDED_SKIPLIST_BDE

#include <bdlf_overloaded.h>
#include <bdls_filesystemutil.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>
#include <bsl_vector.h>
#include <fstream>
#include <skipnode.h>
#include <stm_adapter.h>
#include <utility>
#include <variant>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

struct SkipList_Mod {
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::shared_ptr<SkipNode<T1, T2>>
  findPred_go(F0 &&ltK, unsigned int fuel,
              bsl::shared_ptr<SkipNode<T1, T2>> curr, const T1 &target,
              unsigned int level) {
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = bsl::move(curr);
    unsigned int _loop_fuel = bsl::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return _loop_curr;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[level]));
        if (nextOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
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
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::shared_ptr<SkipNode<T1, T2>>
  findPred(F0 &&ltK, bsl::shared_ptr<SkipNode<T1, T2>> curr, const T1 &target,
           unsigned int level) {
    return findPred_go<T1, T2>(ltK, 10000u, curr, target, level);
  }
  template <typename t_K, typename t_V> struct SkipList {
    bsl::shared_ptr<SkipNode<t_K, t_V>> slHead;
    unsigned int slMaxLevel;
    stm::TVar<unsigned int> slLevel;
    stm::TVar<unsigned int> slLength;
  };
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static SkipPath<T1, T2>
  findPath_aux(F0 &&ltK, bsl::shared_ptr<SkipNode<T1, T2>> curr,
               const T1 &target, unsigned int level, SkipPath<T1, T2> path) {
    unsigned int _loop_level = bsl::move(level);
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = bsl::move(curr);
    while (true) {
      bsl::shared_ptr<SkipNode<T1, T2>> pred =
          findPred<T1, T2>(ltK, _loop_curr, target, _loop_level);
      path.set(_loop_level, pred);
      if (_loop_level <= 0) {
        return path;
      } else {
        unsigned int level_ = _loop_level - 1;
        _loop_level = level_;
        _loop_curr = bsl::move(pred);
      }
    }
  }
  template <typename T1, typename T2>
  static void linkAtLevel(bsl::shared_ptr<SkipNode<T1, T2>> pred,
                          bsl::shared_ptr<SkipNode<T1, T2>> newNode,
                          unsigned int level) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> oldNext = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred->forward[level]));
    stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level],
        opt_to_ptr(
            bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(newNode)));
    stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
        bsl::move(newNode)->forward[level], opt_to_ptr(bsl::move(oldNext)));
    return;
  }
  template <typename T1, typename T2>
  static void
  linkNode_aux(SkipPath<T1, T2> path, bsl::shared_ptr<SkipNode<T1, T2>>,
               bsl::shared_ptr<SkipNode<T1, T2>> newNode, unsigned int level) {
    unsigned int _loop_level = bsl::move(level);
    while (true) {
      bsl::shared_ptr<SkipNode<T1, T2>> pred = path.get(_loop_level);
      linkAtLevel<T1, T2>(pred, newNode, _loop_level);
      if (_loop_level <= 0) {
        return;
      } else {
        unsigned int level_ = _loop_level - 1;
        _loop_level = level_;
      }
    }
    return;
  }
  template <typename T1, typename T2>
  static void extendPath_aux(SkipPath<T1, T2> path,
                             bsl::shared_ptr<SkipNode<T1, T2>> head,
                             unsigned int level, unsigned int maxLevel) {
    unsigned int _loop_level = bsl::move(level);
    while (true) {
      if (_loop_level <= 0) {
        path.set(0u, head);
        return;
      } else {
        unsigned int level_ = _loop_level - 1;
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
                         bsl::shared_ptr<SkipNode<T1, T2>> head,
                         unsigned int needed, unsigned int currentMax) {
    if (needed <= (currentMax + 1)) {
      return;
    } else {
      extendPath_aux<T1, T2>(path, head,
                             (((needed - 1u) > needed ? 0 : (needed - 1u))),
                             (currentMax + 1u));
      return;
    }
  }
  template <typename T1, typename T2>
  static void linkNode(SkipPath<T1, T2> path,
                       bsl::shared_ptr<SkipNode<T1, T2>> head,
                       bsl::shared_ptr<SkipNode<T1, T2>> newNode) {
    unsigned int lvl = newNode->level;
    linkNode_aux<T1, T2>(path, head, newNode, lvl);
    return;
  }
  template <typename T1, typename T2>
  static void unlinkAtLevel(bsl::shared_ptr<SkipNode<T1, T2>> pred,
                            bsl::shared_ptr<SkipNode<T1, T2>> target,
                            unsigned int level) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> targetNext =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            target->forward[level]));
    stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level], opt_to_ptr(bsl::move(targetNext)));
    return;
  }
  template <typename T1, typename T2>
  static void unlinkNode_aux(SkipPath<T1, T2> path,
                             bsl::shared_ptr<SkipNode<T1, T2>> target,
                             unsigned int level) {
    unsigned int _loop_level = bsl::move(level);
    while (true) {
      bsl::shared_ptr<SkipNode<T1, T2>> pred = path.get(_loop_level);
      unlinkAtLevel<T1, T2>(pred, target, _loop_level);
      if (_loop_level <= 0) {
        return;
      } else {
        unsigned int level_ = _loop_level - 1;
        _loop_level = level_;
      }
    }
    return;
  }
  template <typename T1, typename T2>
  static void unlinkNode(SkipPath<T1, T2> path,
                         bsl::shared_ptr<SkipNode<T1, T2>> target) {
    unsigned int lvl = target->level;
    unlinkNode_aux<T1, T2>(path, target, lvl);
    return;
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bool findKey_aux(F0 &&ltK, F1 &&eqK,
                          bsl::shared_ptr<SkipNode<T1, T2>> curr,
                          const T1 &target, unsigned int level) {
    unsigned int _loop_level = bsl::move(level);
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = bsl::move(curr);
    while (true) {
      bsl::shared_ptr<SkipNode<T1, T2>> pred =
          findPred<T1, T2>(ltK, _loop_curr, target, _loop_level);
      if (_loop_level <= 0) {
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                bsl::move(pred)->forward[0u]));
        if (nextOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
          return eqK(node->key, target);
        } else {
          return false;
        }
      } else {
        unsigned int level_ = _loop_level - 1;
        _loop_level = level_;
        _loop_curr = bsl::move(pred);
      }
    }
  }
  template <typename T1, typename T2>
  static unsigned int
  length_aux(unsigned int fuel,
             const bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> &node,
             unsigned int acc) {
    unsigned int _loop_acc = bsl::move(acc);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> _loop_node = node;
    unsigned int _loop_fuel = bsl::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return _loop_acc;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        if (_loop_node.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> n = *_loop_node;
          bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
              stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(n->forward[0u]));
          _loop_acc = (_loop_acc + 1);
          _loop_node = bsl::move(nextOpt);
          _loop_fuel = fuel_;
        } else {
          return _loop_acc;
        }
      }
    }
  }
  template <typename T1, typename T2>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  findLast_aux(unsigned int fuel, bsl::shared_ptr<SkipNode<T1, T2>> curr) {
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = bsl::move(curr);
    unsigned int _loop_fuel = bsl::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(
            _loop_curr);
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[0u]));
        if (nextOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
          _loop_curr = next0;
          _loop_fuel = fuel_;
        } else {
          return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(
              bsl::move(_loop_curr));
        }
      }
    }
  }
  template <typename T1, typename T2>
  static void unlinkFirstFromHead(bsl::shared_ptr<SkipNode<T1, T2>> head,
                                  bsl::shared_ptr<SkipNode<T1, T2>> node,
                                  unsigned int lvl) {
    unsigned int _loop_lvl = bsl::move(lvl);
    while (true) {
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nodeNext =
          ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
              node->forward[_loop_lvl]));
      stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
          head->forward[_loop_lvl], opt_to_ptr(nodeNext));
      if (_loop_lvl <= 0) {
        return;
      } else {
        unsigned int lvl_ = _loop_lvl - 1;
        _loop_lvl = lvl_;
      }
    }
    return;
  }
  template <typename T1, typename T2>
  static void unlinkNodeAtAllLevels(bsl::shared_ptr<SkipNode<T1, T2>> head,
                                    bsl::shared_ptr<SkipNode<T1, T2>> node,
                                    unsigned int lvl) {
    unsigned int _loop_lvl = bsl::move(lvl);
    while (true) {
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nodeNext =
          ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
              node->forward[_loop_lvl]));
      stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
          head->forward[_loop_lvl], opt_to_ptr(nodeNext));
      if (_loop_lvl <= 0) {
        return;
      } else {
        unsigned int lvl_ = _loop_lvl - 1;
        _loop_lvl = lvl_;
      }
    }
    return;
  }
  template <typename T1, typename T2>
  static unsigned int removeAll_aux(unsigned int fuel,
                                    bsl::shared_ptr<SkipNode<T1, T2>> head,
                                    unsigned int acc) {
    unsigned int _loop_acc = bsl::move(acc);
    unsigned int _loop_fuel = bsl::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return _loop_acc;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                head->forward[0u]));
        if (firstOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
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
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  next(bsl::shared_ptr<SkipNode<T1, T2>> pair) {
    return ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pair->forward[0u]));
  }
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  findPrev_aux(F0 &&eqK, unsigned int fuel,
               bsl::shared_ptr<SkipNode<T1, T2>> curr,
               bsl::shared_ptr<SkipNode<T1, T2>> _x, const T1 &target) {
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_x = bsl::move(_x);
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = bsl::move(curr);
    unsigned int _loop_fuel = bsl::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[0u]));
        if (nextOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
          if (eqK(next0->key, target)) {
            return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(
                bsl::move(_loop_curr));
          } else {
            bsl::shared_ptr<SkipNode<T1, T2>> _next_curr = next0;
            _loop_x = bsl::move(_loop_curr);
            _loop_fuel = fuel_;
            _loop_curr = bsl::move(_next_curr);
          }
        } else {
          return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
        }
      }
    }
  }
  template <typename T1, typename T2>
  static T1 key(bsl::shared_ptr<SkipNode<T1, T2>> pair) {
    return pair->key;
  }
  template <typename T1, typename T2>
  static T2 data(bsl::shared_ptr<SkipNode<T1, T2>> pair) {
    return stm::readTVar<T2>(pair->value);
  }
  static inline const unsigned int e_SUCCESS = 0u;
  static inline const unsigned int e_NOT_FOUND = 1u;
  static inline const unsigned int e_DUPLICATE = 2u;
  static inline const unsigned int e_INVALID = 3u;
  template <typename T1, typename T2>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_next(bsl::shared_ptr<SkipNode<T1, T2>> pair) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
        next<T1, T2>(pair);
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      return bsl::make_pair(
          e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2>
  static SkipList<T1, T2> create(const T1 &dummyKey, const T2 &dummyVal) {
    bsl::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal, (((16u - 1u) > 16u ? 0 : (16u - 1u))));
    stm::TVar<unsigned int> lvlTV = stm::newTVar(0u);
    stm::TVar<unsigned int> lenTV = stm::newTVar(0u);
    return SkipList<T1, T2>{headNode, 16u, lvlTV, lenTV};
  }
  template <typename T1, typename T2>
  static SkipList<T1, T2> createIO(const T1 &dummyKey, const T2 &dummyVal) {
    return stm::atomically([&] { return create<T1, T2>(dummyKey, dummyVal); });
  }
};

#endif // INCLUDED_SKIPLIST_BDE
