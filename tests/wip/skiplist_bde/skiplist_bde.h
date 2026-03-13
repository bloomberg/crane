#ifndef INCLUDED_SKIPLIST_BDE
#define INCLUDED_SKIPLIST_BDE

#include <bdlf_overloaded.h>
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
#include <mini_stm.h>
#include <skipnode.h>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <class F, class R, class... Args>
concept MapsTo = requires(F &f, Args &...a) {
  {
    bsl::invoke(static_cast<F &>(f), static_cast<Args &>(a)...)
  } -> convertible_to<R>;
};

struct PeanoNat {
  __attribute__((pure)) static bool eqb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool leb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool ltb(const unsigned int n,
                                        const unsigned int m);
};
struct STM {};
struct TVar {};
template <typename K, typename V> struct SkipList {
  bsl::shared_ptr<SkipNode<K, V>> slHead;
  unsigned int slMaxLevel;
  bsl::shared_ptr<stm::TVar<unsigned int>> slLevel;
  bsl::shared_ptr<stm::TVar<unsigned int>> slLength;
  template <MapsTo<bool, K, K> F0>
  __attribute__((pure)) SkipPath<K, V> findPath(F0 &&ltK,
                                                const K target) const {
    unsigned int lvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    SkipPath<K, V> path = SkipPath<K, V>{};
    return SkipList<int, int>::template findPath_aux<K, V>(
        ltK, this->SkipList::slHead, target, lvl, path);
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) bsl::optional<V> lookup(F0 &&ltK, F1 &&eqK,
                                                const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        V v = stm::readTVar<V>(node->value);
        return bsl::make_optional<V>(v);
      } else {
        return bsl::nullopt;
      }
    } else {
      return bsl::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) void insert(F0 &&ltK, F1 &&eqK, const K k, const V v,
                                    const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        return stm::writeTVar<V>(existing->value, v);
      } else {
        bsl::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(k, v, newLevel);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&](void) {
          if (PeanoNat::ltb(curLvl, newLevel)) {
            return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                                newLevel);
          } else {
            return;
          }
        }();
        unsigned int len =
            stm::readTVar<unsigned int>(this->SkipList::slLength);
        return stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                            (len + 1));
      }
    } else {
      bsl::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&](void) {
        if (PeanoNat::ltb(curLvl, newLevel)) {
          return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                              newLevel);
        } else {
          return;
        }
      }();
      unsigned int len = stm::readTVar<unsigned int>(this->SkipList::slLength);
      return stm::writeTVar<unsigned int>(this->SkipList::slLength, (len + 1));
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) void remove(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        unsigned int curLvl =
            stm::readTVar<unsigned int>(this->SkipList::slLevel);
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (node->level + 1), curLvl);
        SkipList<int, int>::template unlinkNode<K, V>(path, node);
        unsigned int len =
            stm::readTVar<unsigned int>(this->SkipList::slLength);
        return stm::writeTVar<unsigned int>(
            this->SkipList::slLength, (((len - 1u) > len ? 0 : (len - 1u))));
      } else {
        return;
      }
    } else {
      return;
    }
  }
  __attribute__((pure)) bsl::optional<bsl::pair<K, V>> minimum() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      V v = stm::readTVar<V>(node->value);
      return bsl::make_optional<bsl::pair<K, V>>(bsl::make_pair(node->key, v));
    } else {
      return bsl::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) bool memberFast(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) bool member(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  __attribute__((pure)) bool isEmpty() const {
    unsigned int len = stm::readTVar<unsigned int>(this->SkipList::slLength);
    return PeanoNat::eqb(len, 0u);
  }
  __attribute__((pure)) unsigned int length() const {
    return stm::readTVar<unsigned int>(this->SkipList::slLength);
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) bool exists_(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  __attribute__((pure)) bsl::optional<bsl::pair<K, V>> popFront() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level,
          (((16u - 1u) > 16u ? 0 : (16u - 1u))));
      unsigned int len = stm::readTVar<unsigned int>(this->SkipList::slLength);
      stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                   (((len - 1u) > len ? 0 : (len - 1u))));
      V v = stm::readTVar<V>(node->value);
      return bsl::make_optional<bsl::pair<K, V>>(bsl::make_pair(node->key, v));
    } else {
      return bsl::nullopt;
    }
  }
  __attribute__((pure)) unsigned int removeAll() const {
    unsigned int count = SkipList<int, int>::template removeAll_aux<K, V>(
        10000u, this->SkipList::slHead, (((16u - 1u) > 16u ? 0 : (16u - 1u))),
        0u);
    stm::writeTVar<unsigned int>(this->SkipList::slLength, 0u);
    stm::writeTVar<unsigned int>(this->SkipList::slLevel, 0u);
    return count;
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) void add(F0 &&ltK, F1 &&eqK, const K k, const V v,
                                 const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        return stm::writeTVar<V>(existing->value, v);
      } else {
        bsl::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(k, v, newLevel);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&](void) {
          if (PeanoNat::ltb(curLvl, newLevel)) {
            return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                                newLevel);
          } else {
            return;
          }
        }();
        unsigned int len =
            stm::readTVar<unsigned int>(this->SkipList::slLength);
        return stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                            (len + 1));
      }
    } else {
      bsl::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&](void) {
        if (PeanoNat::ltb(curLvl, newLevel)) {
          return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                              newLevel);
        } else {
          return;
        }
      }();
      unsigned int len = stm::readTVar<unsigned int>(this->SkipList::slLength);
      return stm::writeTVar<unsigned int>(this->SkipList::slLength, (len + 1));
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) bool addUnique(F0 &&ltK, F1 &&eqK, const K k, const V v,
                                       const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        return false;
      } else {
        bsl::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(k, v, newLevel);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&](void) {
          if (PeanoNat::ltb(curLvl, newLevel)) {
            return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                                newLevel);
          } else {
            return;
          }
        }();
        unsigned int len =
            stm::readTVar<unsigned int>(this->SkipList::slLength);
        stm::writeTVar<unsigned int>(this->SkipList::slLength, (len + 1));
        return true;
      }
    } else {
      bsl::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&](void) {
        if (PeanoNat::ltb(curLvl, newLevel)) {
          return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                              newLevel);
        } else {
          return;
        }
      }();
      unsigned int len = stm::readTVar<unsigned int>(this->SkipList::slLength);
      stm::writeTVar<unsigned int>(this->SkipList::slLength, (len + 1));
      return true;
    }
  }
  __attribute__((pure)) unsigned int bde_removeAll() const {
    return this->removeAll();
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  __attribute__((pure)) bool bde_exists(F0 &&ltK, F1 &&eqK,
                                        const K key0) const {
    unsigned int lvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, key0, lvl);
  }
  __attribute__((pure)) bool bde_isEmpty() const { return this->isEmpty(); }
  __attribute__((pure)) unsigned int bde_length() const {
    return this->length();
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bsl::shared_ptr<SkipNode<T1, T2>>
  findPred_go(F0 &&ltK, const unsigned int fuel,
              const bsl::shared_ptr<SkipNode<T1, T2>> curr, const T1 target,
              const unsigned int level) {
    if (fuel <= 0) {
      return curr;
    } else {
      unsigned int fuel_ = fuel - 1;
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
          ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
              curr->forward[level]));
      if (nextOpt.has_value()) {
        bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        if (ltK(bsl::move(next0)->key, target)) {
          return SkipList<int, int>::template findPred_go<T1, T2>(
              ltK, fuel_, bsl::move(next0), target, level);
        } else {
          return curr;
        }
      } else {
        return curr;
      }
    }
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bsl::shared_ptr<SkipNode<T1, T2>>
  findPred(F0 &&ltK, const bsl::shared_ptr<SkipNode<T1, T2>> curr,
           const T1 target, const unsigned int level) {
    return SkipList<int, int>::template findPred_go<T1, T2>(ltK, 10000u, curr,
                                                            target, level);
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static SkipPath<T1, T2>
  findPath_aux(F0 &&ltK, const bsl::shared_ptr<SkipNode<T1, T2>> curr,
               const T1 target, const unsigned int level,
               const SkipPath<T1, T2> path) {
    bsl::shared_ptr<SkipNode<T1, T2>> pred =
        SkipList<int, int>::template findPred<T1, T2>(ltK, curr, target, level);
    path.set(level, pred);
    if (level <= 0) {
      return path;
    } else {
      unsigned int level_ = level - 1;
      return SkipList<int, int>::template findPath_aux<T1, T2>(
          ltK, pred, target, level_, path);
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  linkAtLevel(const bsl::shared_ptr<SkipNode<T1, T2>> pred,
              const bsl::shared_ptr<SkipNode<T1, T2>> newNode,
              const unsigned int level) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> oldNext = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred->forward[level]));
    stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level],
        opt_to_ptr(
            bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(newNode)));
    return stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
        newNode->forward[level], opt_to_ptr(oldNext));
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  linkNode_aux(const SkipPath<T1, T2> path,
               const bsl::shared_ptr<SkipNode<T1, T2>> head,
               const bsl::shared_ptr<SkipNode<T1, T2>> newNode,
               const unsigned int level) {
    bsl::shared_ptr<SkipNode<T1, T2>> pred = path.get(level);
    SkipList<int, int>::template linkAtLevel<T1, T2>(pred, newNode, level);
    if (level <= 0) {
      return;
    } else {
      unsigned int level_ = level - 1;
      return SkipList<int, int>::template linkNode_aux<T1, T2>(
          path, head, newNode, bsl::move(level_));
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  extendPath_aux(const SkipPath<T1, T2> path,
                 const bsl::shared_ptr<SkipNode<T1, T2>> head,
                 const unsigned int level, const unsigned int maxLevel) {
    if (level <= 0) {
      return path.set(0u, head);
    } else {
      unsigned int level_ = level - 1;
      path.set(level, head);
      if (PeanoNat::leb(maxLevel, level_)) {
        return SkipList<int, int>::template extendPath_aux<T1, T2>(
            path, head, level_, maxLevel);
      } else {
        return;
      }
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  extendPath(const SkipPath<T1, T2> path,
             const bsl::shared_ptr<SkipNode<T1, T2>> head,
             const unsigned int needed, const unsigned int currentMax) {
    if (PeanoNat::leb(needed, (currentMax + 1))) {
      return;
    } else {
      return SkipList<int, int>::template extendPath_aux<T1, T2>(
          path, head, (((needed - 1u) > needed ? 0 : (needed - 1u))),
          (bsl::move(currentMax) + 1u));
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  linkNode(const SkipPath<T1, T2> path,
           const bsl::shared_ptr<SkipNode<T1, T2>> head,
           const bsl::shared_ptr<SkipNode<T1, T2>> newNode) {
    unsigned int lvl = newNode->level;
    return SkipList<int, int>::template linkNode_aux<T1, T2>(
        path, head, newNode, bsl::move(lvl));
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  unlinkAtLevel(const bsl::shared_ptr<SkipNode<T1, T2>> pred,
                const bsl::shared_ptr<SkipNode<T1, T2>> target,
                const unsigned int level) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> targetNext =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            target->forward[level]));
    return stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level], opt_to_ptr(bsl::move(targetNext)));
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  unlinkNode_aux(const SkipPath<T1, T2> path,
                 const bsl::shared_ptr<SkipNode<T1, T2>> target,
                 const unsigned int level) {
    bsl::shared_ptr<SkipNode<T1, T2>> pred = path.get(level);
    SkipList<int, int>::template unlinkAtLevel<T1, T2>(pred, target, level);
    if (level <= 0) {
      return;
    } else {
      unsigned int level_ = level - 1;
      return SkipList<int, int>::template unlinkNode_aux<T1, T2>(
          path, target, bsl::move(level_));
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  unlinkNode(const SkipPath<T1, T2> path,
             const bsl::shared_ptr<SkipNode<T1, T2>> target) {
    unsigned int lvl = target->level;
    return SkipList<int, int>::template unlinkNode_aux<T1, T2>(path, target,
                                                               bsl::move(lvl));
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  __attribute__((pure)) static bool
  findKey_aux(F0 &&ltK, F1 &&eqK, const bsl::shared_ptr<SkipNode<T1, T2>> curr,
              const T1 target, const unsigned int level) {
    bsl::shared_ptr<SkipNode<T1, T2>> pred =
        SkipList<int, int>::template findPred<T1, T2>(ltK, curr, target, level);
    if (level <= 0) {
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
          ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
              bsl::move(pred)->forward[0u]));
      if (nextOpt.has_value()) {
        bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
        return eqK(bsl::move(node)->key, target);
      } else {
        return false;
      }
    } else {
      unsigned int level_ = level - 1;
      return SkipList<int, int>::template findKey_aux<T1, T2>(
          ltK, eqK, pred, target, bsl::move(level_));
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  findLast_aux(const unsigned int fuel,
               const bsl::shared_ptr<SkipNode<T1, T2>> curr) {
    if (fuel <= 0) {
      return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(curr);
    } else {
      unsigned int fuel_ = fuel - 1;
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
          stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(curr->forward[0u]));
      if (nextOpt.has_value()) {
        bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        return SkipList<int, int>::template findLast_aux<T1, T2>(fuel_, next0);
      } else {
        return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(curr);
      }
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  unlinkFirstFromHead(const bsl::shared_ptr<SkipNode<T1, T2>> head,
                      const bsl::shared_ptr<SkipNode<T1, T2>> node,
                      const unsigned int nodeLevel, const unsigned int lvl) {
    if (lvl <= 0) {
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nodeNext = ptr_to_opt(
          stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(node->forward[0u]));
      return stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
          head->forward[0u], opt_to_ptr(bsl::move(nodeNext)));
    } else {
      unsigned int lvl_ = lvl - 1;
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> headNext = ptr_to_opt(
          stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(head->forward[lvl]));
      [&](void) {
        if (headNext.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> _x = *headNext;
          if (PeanoNat::leb(lvl, nodeLevel)) {
            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nodeNext =
                ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                    node->forward[lvl]));
            return stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                head->forward[lvl], opt_to_ptr(bsl::move(nodeNext)));
          } else {
            return;
          }
        } else {
          return;
        }
      }();
      return SkipList<int, int>::template unlinkFirstFromHead<T1, T2>(
          head, node, nodeLevel, lvl_);
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static void
  unlinkNodeAtAllLevels(const bsl::shared_ptr<SkipNode<T1, T2>> head,
                        const bsl::shared_ptr<SkipNode<T1, T2>> node,
                        const unsigned int lvl) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> headNext = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(head->forward[lvl]));
    [&](void) {
      if (headNext.has_value()) {
        bsl::shared_ptr<SkipNode<T1, T2>> _x = *headNext;
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nodeNext =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                node->forward[lvl]));
        return stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            head->forward[lvl], opt_to_ptr(bsl::move(nodeNext)));
      } else {
        return;
      }
    }();
    if (lvl <= 0) {
      return;
    } else {
      unsigned int lvl_ = lvl - 1;
      return SkipList<int, int>::template unlinkNodeAtAllLevels<T1, T2>(
          head, node, bsl::move(lvl_));
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static unsigned int
  removeAll_aux(const unsigned int fuel,
                const bsl::shared_ptr<SkipNode<T1, T2>> head,
                const unsigned int maxLvl, const unsigned int acc) {
    if (fuel <= 0) {
      return bsl::move(acc);
    } else {
      unsigned int fuel_ = fuel - 1;
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt = ptr_to_opt(
          stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(head->forward[0u]));
      if (firstOpt.has_value()) {
        bsl::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
        SkipList<int, int>::template unlinkNodeAtAllLevels<T1, T2>(
            head, bsl::move(node), maxLvl);
        return SkipList<int, int>::template removeAll_aux<T1, T2>(
            fuel_, head, maxLvl, (acc + 1));
      } else {
        return acc;
      }
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  next(const bsl::shared_ptr<SkipNode<T1, T2>> pair) {
    return ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pair->forward[0u]));
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  findPrev_aux(F0 &&eqK, const unsigned int fuel,
               const bsl::shared_ptr<SkipNode<T1, T2>> curr,
               const bsl::shared_ptr<SkipNode<T1, T2>> _x, const T1 target) {
    if (fuel <= 0) {
      return bsl::nullopt;
    } else {
      unsigned int fuel_ = fuel - 1;
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
          stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(curr->forward[0u]));
      if (nextOpt.has_value()) {
        bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        if (eqK(next0->key, target)) {
          return bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(curr);
        } else {
          return SkipList<int, int>::template findPrev_aux<T1, T2>(
              eqK, fuel_, next0, curr, target);
        }
      } else {
        return bsl::nullopt;
      }
    }
  }
  template <typename T1, typename T2>
  static T1 key(const bsl::shared_ptr<SkipNode<T1, T2>> _x0) {
    return _x0->key;
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static T2
  data(const bsl::shared_ptr<SkipNode<T1, T2>> _x0) {
    return stm::readTVar<T2>(_x0->value);
  }
  static inline const unsigned int e_SUCCESS = 0u;
  static inline const unsigned int e_NOT_FOUND = 1u;
  static inline const unsigned int e_DUPLICATE = 2u;
  static inline const unsigned int e_INVALID = 3u;
  template <typename T1, typename T2>
  __attribute__((pure)) static bsl::pair<
      unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_next(const bsl::shared_ptr<SkipNode<T1, T2>> pair) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
        SkipList<int, int>::template next<T1, T2>(pair);
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      return bsl::make_pair(
          SkipList<int, int>::e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND, bsl::nullopt);
    }
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static bsl::shared_ptr<SkipList<T1, T2>>
  create(const T1 dummyKey, const T2 dummyVal) {
    bsl::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal, (((16u - 1u) > 16u ? 0 : (16u - 1u))));
    bsl::shared_ptr<stm::TVar<unsigned int>> lvlTV =
        stm::newTVar<unsigned int>(0u);
    bsl::shared_ptr<stm::TVar<unsigned int>> lenTV =
        stm::newTVar<unsigned int>(0u);
    return bsl::make_shared<SkipList<T1, T2>>(
        SkipList<T1, T2>{headNode, 16u, lvlTV, lenTV});
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static bsl::shared_ptr<SkipList<T1, T2>>
  createIO(const T1 dummyKey, const T2 dummyVal) {
    return stm::atomically([&] {
      return SkipList<int, int>::template create<T1, T2>(dummyKey, dummyVal);
    });
  }
};

#endif // INCLUDED_SKIPLIST_BDE
