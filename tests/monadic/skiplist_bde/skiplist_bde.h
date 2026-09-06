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

struct SkipList {
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
  template <typename t_K, typename t_V> struct SkipList0 {
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
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static SkipPath<T1, T2> findPath(F0 &&ltK, const SkipList0<T1, T2> &sl,
                                   const T1 &target) {
    unsigned int lvl = stm::readTVar(sl.slLevel);
    SkipPath<T1, T2> path = SkipPath<T1, T2>{};
    return findPath_aux<T1, T2>(ltK, sl.slHead, target, lvl, bsl::move(path));
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bsl::optional<T2> lookup(F0 &&ltK, F1 &&eqK, const T1 &k,
                                  const SkipList0<T1, T2> &sl) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      if (eqK(node->key, k)) {
        T2 v = stm::readTVar<T2>(node->value);
        return bsl::make_optional<T2>(v);
      } else {
        return bsl::optional<T2>();
      }
    } else {
      return bsl::optional<T2>();
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
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static void insert(F0 &&ltK, F1 &&eqK, const T1 &k, const T2 &v,
                     const SkipList0<T1, T2> &sl, unsigned int newLevel) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    unsigned int curLvl = stm::readTVar(sl.slLevel);
    extendPath<T1, T2>(path, sl.slHead, (newLevel + 1), curLvl);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        stm::writeTVar<T2>(existing->value, v);
        return;
      } else {
        bsl::shared_ptr<SkipNode<T1, T2>> newN =
            SkipNode<T1, T2>::create(k, v, newLevel);
        linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
        if (curLvl < newLevel) {
          stm::writeTVar(sl.slLevel, newLevel);
          return;
        } else {
          return;
        }
      }
    } else {
      bsl::shared_ptr<SkipNode<T1, T2>> newN =
          SkipNode<T1, T2>::create(k, v, newLevel);
      linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
      if (curLvl < newLevel) {
        stm::writeTVar(sl.slLevel, newLevel);
        return;
      } else {
        return;
      }
    }
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
  static void remove(F0 &&ltK, F1 &&eqK, const T1 &k,
                     const SkipList0<T1, T2> &sl) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      if (eqK(node->key, k)) {
        unsigned int curLvl = stm::readTVar(sl.slLevel);
        extendPath<T1, T2>(path, sl.slHead, (node->level + 1), curLvl);
        unlinkNode<T1, T2>(bsl::move(path), node);
        return;
      } else {
        return;
      }
    } else {
      return;
    }
  }
  template <typename T1, typename T2>
  static bsl::optional<bsl::pair<T1, T2>> minimum(const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
      T2 v = stm::readTVar<T2>(node->value);
      return bsl::make_optional<bsl::pair<T1, T2>>(
          bsl::make_pair(node->key, v));
    } else {
      return bsl::optional<bsl::pair<T1, T2>>();
    }
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
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bool memberFast(F0 &&ltK, F1 &&eqK, const T1 &k,
                         const SkipList0<T1, T2> &sl) {
    unsigned int lvl = stm::readTVar(sl.slLevel);
    return findKey_aux<T1, T2>(ltK, eqK, sl.slHead, k, lvl);
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bool member(F0 &&ltK, F1 &&eqK, const T1 &k,
                     const SkipList0<T1, T2> &sl) {
    unsigned int lvl = stm::readTVar(sl.slLevel);
    return findKey_aux<T1, T2>(ltK, eqK, sl.slHead, k, lvl);
  }
  template <typename T1, typename T2>
  static bool isEmpty(const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    return [=]() mutable -> bool {
      if (firstOpt.has_value()) {
        bsl::shared_ptr<SkipNode<T1, T2>> _x = *firstOpt;
        return false;
      } else {
        return true;
      }
    }();
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
  static unsigned int length(const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    return length_aux<T1, T2>(10000u, bsl::move(firstOpt), 0u);
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bool exists_(F0 &&ltK, F1 &&eqK, const T1 &k,
                      const SkipList0<T1, T2> &sl) {
    unsigned int lvl = stm::readTVar(sl.slLevel);
    return findKey_aux<T1, T2>(ltK, eqK, sl.slHead, k, lvl);
  }
  template <typename T1, typename T2>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  front(const SkipList0<T1, T2> &sl) {
    return ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
        sl.slHead->forward[0u]));
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
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  back(const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> first = *firstOpt;
      return findLast_aux<T1, T2>(10000u, first);
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
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
  static bsl::optional<bsl::pair<T1, T2>>
  popFront(const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
      unlinkFirstFromHead<T1, T2>(sl.slHead, node, node->level);
      T2 v = stm::readTVar<T2>(node->value);
      return bsl::make_optional<bsl::pair<T1, T2>>(
          bsl::make_pair(node->key, v));
    } else {
      return bsl::optional<bsl::pair<T1, T2>>();
    }
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
  static unsigned int removeAll(const SkipList0<T1, T2> &sl) {
    unsigned int count = removeAll_aux<T1, T2>(10000u, sl.slHead, 0u);
    stm::writeTVar(sl.slLevel, 0u);
    return count;
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static void add(F0 &&ltK, F1 &&eqK, const T1 &k, const T2 &v,
                  const SkipList0<T1, T2> &sl, unsigned int newLevel) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    unsigned int curLvl = stm::readTVar(sl.slLevel);
    extendPath<T1, T2>(path, sl.slHead, (newLevel + 1), curLvl);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        stm::writeTVar<T2>(existing->value, v);
        return;
      } else {
        bsl::shared_ptr<SkipNode<T1, T2>> newN =
            SkipNode<T1, T2>::create(k, v, newLevel);
        linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
        if (curLvl < newLevel) {
          stm::writeTVar(sl.slLevel, newLevel);
          return;
        } else {
          return;
        }
      }
    } else {
      bsl::shared_ptr<SkipNode<T1, T2>> newN =
          SkipNode<T1, T2>::create(k, v, newLevel);
      linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
      if (curLvl < newLevel) {
        stm::writeTVar(sl.slLevel, newLevel);
        return;
      } else {
        return;
      }
    }
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bool addUnique(F0 &&ltK, F1 &&eqK, const T1 &k, const T2 &v,
                        const SkipList0<T1, T2> &sl, unsigned int newLevel) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    unsigned int curLvl = stm::readTVar(sl.slLevel);
    extendPath<T1, T2>(path, sl.slHead, (newLevel + 1), curLvl);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        return false;
      } else {
        bsl::shared_ptr<SkipNode<T1, T2>> newN =
            SkipNode<T1, T2>::create(k, v, newLevel);
        linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
        [&]() -> void {
          if (curLvl < newLevel) {
            stm::writeTVar(sl.slLevel, newLevel);
            return;
          } else {
            return;
          }
        }();
        return true;
      }
    } else {
      bsl::shared_ptr<SkipNode<T1, T2>> newN =
          SkipNode<T1, T2>::create(k, v, newLevel);
      linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
      [&]() -> void {
        if (curLvl < newLevel) {
          stm::writeTVar(sl.slLevel, newLevel);
          return;
        } else {
          return;
        }
      }();
      return true;
    }
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  find(F0 &&ltK, F1 &&eqK, const T1 &k, const SkipList0<T1, T2> &sl) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      if (eqK(node->key, k)) {
        return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node);
      } else {
        return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
      }
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
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
               bsl::shared_ptr<SkipNode<T1, T2>>, const T1 &target) {
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
            _loop_fuel = fuel_;
            _loop_curr = bsl::move(_next_curr);
          }
        } else {
          return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
        }
      }
    }
  }
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  previous(F0 &&eqK, bsl::shared_ptr<SkipNode<T1, T2>> pair,
           const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> first = *firstOpt;
      if (eqK(first->key, pair->key)) {
        return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
      } else {
        return findPrev_aux<T1, T2>(eqK, 10000u, first, sl.slHead, pair->key);
      }
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
    }
  }
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  findLowerBound(F0 &&ltK, const T1 &k, const SkipList0<T1, T2> &sl) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node);
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
    }
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  findUpperBound(F0 &&ltK, F1 &&eqK, const T1 &k, const SkipList0<T1, T2> &sl) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      if (eqK(node->key, k)) {
        return ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            node->forward[0u]));
      } else {
        return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node);
      }
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
    }
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bool removePair(F0 &&ltK, F1 &&eqK,
                         bsl::shared_ptr<SkipNode<T1, T2>> pair,
                         const SkipList0<T1, T2> &sl) {
    T1 k = pair->key;
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, k);
    unsigned int curLvl = stm::readTVar(sl.slLevel);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      if (eqK(node->key, k)) {
        extendPath<T1, T2>(path, sl.slHead, (node->level + 1), curLvl);
        unlinkNode<T1, T2>(path, node);
        return true;
      } else {
        return false;
      }
    } else {
      return false;
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
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bsl::pair<bsl::shared_ptr<SkipNode<T1, T2>>, bool>
  bde_add(F0 &&ltK, F1 &&eqK, const T1 &key0, const T2 &data0,
          const SkipList0<T1, T2> &sl, unsigned int level) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, key0);
    unsigned int curLvl = stm::readTVar(sl.slLevel);
    extendPath<T1, T2>(path, sl.slHead, (level + 1), curLvl);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> curFront =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    bool isNewFront;
    if (curFront.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> existing = *nextOpt;
      if (eqK(existing->key, key0)) {
        stm::writeTVar<T2>(existing->value, data0);
        return bsl::make_pair(existing, false);
      } else {
        bsl::shared_ptr<SkipNode<T1, T2>> newN =
            SkipNode<T1, T2>::create(key0, data0, level);
        linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
        [&]() -> void {
          if (curLvl < level) {
            stm::writeTVar(sl.slLevel, level);
            return;
          } else {
            return;
          }
        }();
        return bsl::make_pair(newN, isNewFront);
      }
    } else {
      bsl::shared_ptr<SkipNode<T1, T2>> newN =
          SkipNode<T1, T2>::create(key0, data0, level);
      linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
      [&]() -> void {
        if (curLvl < level) {
          stm::writeTVar(sl.slLevel, level);
          return;
        } else {
          return;
        }
      }();
      return bsl::make_pair(newN, isNewFront);
    }
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bsl::pair<
      bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>,
      bool>
  bde_addUnique(F0 &&ltK, F1 &&eqK, const T1 &key0, const T2 &data0,
                const SkipList0<T1, T2> &sl, unsigned int level) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, key0);
    unsigned int curLvl = stm::readTVar(sl.slLevel);
    extendPath<T1, T2>(path, sl.slHead, (level + 1), curLvl);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> curFront =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    bool isNewFront;
    if (curFront.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> existing = *nextOpt;
      if (eqK(existing->key, key0)) {
        return bsl::make_pair(
            bsl::make_pair(e_DUPLICATE,
                           bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>()),
            false);
      } else {
        bsl::shared_ptr<SkipNode<T1, T2>> newN =
            SkipNode<T1, T2>::create(key0, data0, level);
        linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
        [&]() -> void {
          if (curLvl < level) {
            stm::writeTVar(sl.slLevel, level);
            return;
          } else {
            return;
          }
        }();
        return bsl::make_pair(
            bsl::make_pair(
                e_SUCCESS,
                bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(newN)),
            isNewFront);
      }
    } else {
      bsl::shared_ptr<SkipNode<T1, T2>> newN =
          SkipNode<T1, T2>::create(key0, data0, level);
      linkNode<T1, T2>(bsl::move(path), sl.slHead, newN);
      [&]() -> void {
        if (curLvl < level) {
          stm::writeTVar(sl.slLevel, level);
          return;
        } else {
          return;
        }
      }();
      return bsl::make_pair(
          bsl::make_pair(
              e_SUCCESS,
              bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(newN)),
          isNewFront);
    }
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_find(F0 &&ltK, F1 &&eqK, const T1 &key0, const SkipList0<T1, T2> &sl) {
    SkipPath<T1, T2> path = findPath<T1, T2>(ltK, sl, key0);
    bsl::shared_ptr<SkipNode<T1, T2>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      if (eqK(node->key, key0)) {
        return bsl::make_pair(
            e_SUCCESS,
            bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
      } else {
        return bsl::make_pair(
            e_NOT_FOUND, bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
      }
    } else {
      return bsl::make_pair(e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_front(const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> frontOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    if (frontOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *frontOpt;
      return bsl::make_pair(
          e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_back(const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> backOpt = back<T1, T2>(sl);
    if (backOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *backOpt;
      return bsl::make_pair(
          e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_popFront(const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            sl.slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
      unlinkFirstFromHead<T1, T2>(sl.slHead, node, node->level);
      return bsl::make_pair(
          e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static unsigned int bde_remove(F0 &&ltK, F1 &&eqK,
                                 bsl::shared_ptr<SkipNode<T1, T2>> pair,
                                 const SkipList0<T1, T2> &sl) {
    bool result = removePair<T1, T2>(ltK, eqK, pair, sl);
    if (result) {
      return e_SUCCESS;
    } else {
      return e_NOT_FOUND;
    }
  }
  template <typename T1, typename T2>
  static unsigned int bde_removeAll(const SkipList0<T1, T2> &_x0) {
    return removeAll<T1, T2>(_x0);
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bool bde_exists(F0 &&ltK, F1 &&eqK, const T1 &key0,
                         const SkipList0<T1, T2> &sl) {
    unsigned int lvl = stm::readTVar(sl.slLevel);
    return findKey_aux<T1, T2>(ltK, eqK, sl.slHead, key0, lvl);
  }
  template <typename T1, typename T2>
  static bool bde_isEmpty(const SkipList0<T1, T2> &_x0) {
    return isEmpty<T1, T2>(_x0);
  }
  template <typename T1, typename T2>
  static unsigned int bde_length(const SkipList0<T1, T2> &_x0) {
    return length<T1, T2>(_x0);
  }
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
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_previous(F0 &&eqK, bsl::shared_ptr<SkipNode<T1, T2>> pair,
               const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> prevOpt =
        previous<T1, T2>(eqK, pair, sl);
    if (prevOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *prevOpt;
      return bsl::make_pair(
          e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_findLowerBound(F0 &&ltK, const T1 &key0, const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> result =
        findLowerBound<T1, T2>(ltK, key0, sl);
    if (result.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *result;
      return bsl::make_pair(
          e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<bool, F1 &, T1 &, T1 &>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_findUpperBound(F0 &&ltK, F1 &&eqK, const T1 &key0,
                     const SkipList0<T1, T2> &sl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> result =
        findUpperBound<T1, T2>(ltK, eqK, key0, sl);
    if (result.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *result;
      return bsl::make_pair(
          e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2>
  static SkipList0<T1, T2> create(const T1 &dummyKey, const T2 &dummyVal) {
    bsl::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal, (((16u - 1u) > 16u ? 0 : (16u - 1u))));
    stm::TVar<unsigned int> lvlTV = stm::newTVar(0u);
    stm::TVar<unsigned int> lenTV = stm::newTVar(0u);
    return SkipList0<T1, T2>{headNode, 16u, lvlTV, lenTV};
  }
  template <typename T1, typename T2>
  static SkipList0<T1, T2> createIO(const T1 &dummyKey, const T2 &dummyVal) {
    return stm::atomically([&] { return create<T1, T2>(dummyKey, dummyVal); });
  }
};

#endif // INCLUDED_SKIPLIST_BDE
