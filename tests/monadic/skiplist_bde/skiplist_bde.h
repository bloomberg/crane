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
#include <fstream>
#include <skipnode.h>
#include <stm_adapter.h>
#include <variant>

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

template <typename K, typename V> struct SkipList {
  bsl::shared_ptr<SkipNode<K, V>> slHead;
  unsigned int slMaxLevel;
  stm::TVar<unsigned int> slLevel;
  stm::TVar<unsigned int> slLength;
  template <MapsTo<bool, K, K> F0>
  SkipPath<K, V> findPath(F0 &&ltK, const K target) const {
    unsigned int lvl = stm::readTVar(this->SkipList::slLevel);
    SkipPath<K, V> path = SkipPath<K, V>{};
    return SkipList<int, int>::template findPath_aux<K, V>(
        ltK, this->SkipList::slHead, target, lvl, path);
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bsl::optional<V> lookup(F0 &&ltK, F1 &&eqK, const K k) const {
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
        return bsl::optional<V>();
      }
    } else {
      return bsl::optional<V>();
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::monostate insert(F0 &&ltK, F1 &&eqK, const K k, const V v,
                        const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        stm::writeTVar<V>(existing->value, v);
        return std::monostate{};
      } else {
        bsl::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(k, v, newLevel);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        if (curLvl < newLevel) {
          stm::writeTVar(this->SkipList::slLevel, newLevel);
          return std::monostate{};
        } else {
          return std::monostate{};
        }
      }
    } else {
      bsl::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      if (curLvl < newLevel) {
        stm::writeTVar(this->SkipList::slLevel, newLevel);
        return std::monostate{};
      } else {
        return std::monostate{};
      }
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::monostate remove(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (node->level + 1), curLvl);
        SkipList<int, int>::template unlinkNode<K, V>(path, node);
        return std::monostate{};
      } else {
        return std::monostate{};
      }
    } else {
      return std::monostate{};
    }
  }
  bsl::optional<bsl::pair<K, V>> minimum() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      V v = stm::readTVar<V>(node->value);
      return bsl::make_optional<bsl::pair<K, V>>(bsl::make_pair(node->key, v));
    } else {
      return bsl::optional<bsl::pair<K, V>>();
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool memberFast(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = stm::readTVar(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool member(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = stm::readTVar(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  bool isEmpty() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    return [&]() -> bool {
      if (firstOpt.has_value()) {
        bsl::shared_ptr<SkipNode<K, V>> _x = *firstOpt;
        return false;
      } else {
        return true;
      }
    }();
  }
  unsigned int length() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    return SkipList<int, int>::template length_aux<K, V>(10000u, firstOpt, 0u);
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool exists_(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = stm::readTVar(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> front() const {
    return ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
        this->SkipList::slHead->forward[0u]));
  }
  bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> back() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> first = *firstOpt;
      return SkipList<int, int>::template findLast_aux<K, V>(10000u, first);
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>();
    }
  }
  bsl::optional<bsl::pair<K, V>> popFront() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level);
      V v = stm::readTVar<V>(node->value);
      return bsl::make_optional<bsl::pair<K, V>>(bsl::make_pair(node->key, v));
    } else {
      return bsl::optional<bsl::pair<K, V>>();
    }
  }
  unsigned int removeAll() const {
    unsigned int count = SkipList<int, int>::template removeAll_aux<K, V>(
        10000u, this->SkipList::slHead, 0u);
    stm::writeTVar(this->SkipList::slLevel, 0u);
    return count;
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::monostate add(F0 &&ltK, F1 &&eqK, const K k, const V v,
                     const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        stm::writeTVar<V>(existing->value, v);
        return std::monostate{};
      } else {
        bsl::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(k, v, newLevel);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        if (curLvl < newLevel) {
          stm::writeTVar(this->SkipList::slLevel, newLevel);
          return std::monostate{};
        } else {
          return std::monostate{};
        }
      }
    } else {
      bsl::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      if (curLvl < newLevel) {
        stm::writeTVar(this->SkipList::slLevel, newLevel);
        return std::monostate{};
      } else {
        return std::monostate{};
      }
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool addUnique(F0 &&ltK, F1 &&eqK, const K k, const V v,
                 const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
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
        [&]() -> void {
          if (curLvl < newLevel) {
            stm::writeTVar(this->SkipList::slLevel, newLevel);
            return;
          } else {
            return;
          }
        }();
        return true;
      }
    } else {
      bsl::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&]() -> void {
        if (curLvl < newLevel) {
          stm::writeTVar(this->SkipList::slLevel, newLevel);
          return;
        } else {
          return;
        }
      }();
      return true;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> find(F0 &&ltK, F1 &&eqK,
                                                      const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        return bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node);
      } else {
        return bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>();
      }
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>();
    }
  }
  template <MapsTo<bool, K, K> F0>
  bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>
  previous(F0 &&eqK, const bsl::shared_ptr<SkipNode<K, V>> pair) const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> first = *firstOpt;
      if (eqK(first->key, pair->key)) {
        return bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>();
      } else {
        return SkipList<int, int>::template findPrev_aux<K, V>(
            eqK, 10000u, first, this->SkipList::slHead, pair->key);
      }
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>();
    }
  }
  template <MapsTo<bool, K, K> F0>
  bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>
  findLowerBound(F0 &&ltK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      return bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node);
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>();
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>
  findUpperBound(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        return ptr_to_opt(
            stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(node->forward[0u]));
      } else {
        return bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node);
      }
    } else {
      return bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>();
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool removePair(F0 &&ltK, F1 &&eqK,
                  const bsl::shared_ptr<SkipNode<K, V>> pair) const {
    K k = pair->key;
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (node->level + 1), curLvl);
        SkipList<int, int>::template unlinkNode<K, V>(path, node);
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bsl::pair<bsl::shared_ptr<SkipNode<K, V>>, bool>
  bde_add(F0 &&ltK, F1 &&eqK, const K key0, const V data0,
          const unsigned int level) const {
    SkipPath<K, V> path = this->findPath(ltK, key0);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (level + 1), curLvl);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> curFront =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    bool isNewFront;
    if (curFront.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, key0)) {
        stm::writeTVar<V>(existing->value, data0);
        return bsl::make_pair(existing, false);
      } else {
        bsl::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(key0, data0, level);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&]() -> void {
          if (curLvl < level) {
            stm::writeTVar(this->SkipList::slLevel, level);
            return;
          } else {
            return;
          }
        }();
        return bsl::make_pair(newN, isNewFront);
      }
    } else {
      bsl::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(key0, data0, level);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&]() -> void {
        if (curLvl < level) {
          stm::writeTVar(this->SkipList::slLevel, level);
          return;
        } else {
          return;
        }
      }();
      return bsl::make_pair(newN, isNewFront);
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bsl::pair<
      bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>>,
      bool>
  bde_addUnique(F0 &&ltK, F1 &&eqK, const K key0, const V data0,
                const unsigned int level) const {
    SkipPath<K, V> path = this->findPath(ltK, key0);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (level + 1), curLvl);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> curFront =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    bool isNewFront;
    if (curFront.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, key0)) {
        return bsl::make_pair(
            bsl::make_pair(SkipList<int, int>::e_DUPLICATE,
                           bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>()),
            false);
      } else {
        bsl::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(key0, data0, level);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&]() -> void {
          if (curLvl < level) {
            stm::writeTVar(this->SkipList::slLevel, level);
            return;
          } else {
            return;
          }
        }();
        return bsl::make_pair(
            bsl::make_pair(
                SkipList<int, int>::e_SUCCESS,
                bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(newN)),
            isNewFront);
      }
    } else {
      bsl::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(key0, data0, level);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&]() -> void {
        if (curLvl < level) {
          stm::writeTVar(this->SkipList::slLevel, level);
          return;
        } else {
          return;
        }
      }();
      return bsl::make_pair(
          bsl::make_pair(
              SkipList<int, int>::e_SUCCESS,
              bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(newN)),
          isNewFront);
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>>
  bde_find(F0 &&ltK, F1 &&eqK, const K key0) const {
    SkipPath<K, V> path = this->findPath(ltK, key0);
    bsl::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, key0)) {
        return bsl::make_pair(
            SkipList<int, int>::e_SUCCESS,
            bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node));
      } else {
        return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                              bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>());
      }
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>());
    }
  }
  bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>>
  bde_front() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> frontOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (frontOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *frontOpt;
      return bsl::make_pair(
          SkipList<int, int>::e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>());
    }
  }
  bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>>
  bde_back() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> backOpt = this->back();
    if (backOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *backOpt;
      return bsl::make_pair(
          SkipList<int, int>::e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>());
    }
  }
  bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>>
  bde_popFront() const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level);
      return bsl::make_pair(
          SkipList<int, int>::e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>());
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  unsigned int bde_remove(F0 &&ltK, F1 &&eqK,
                          const bsl::shared_ptr<SkipNode<K, V>> pair) const {
    bool result = this->removePair(ltK, eqK, pair);
    if (result) {
      return SkipList<int, int>::e_SUCCESS;
    } else {
      return SkipList<int, int>::e_NOT_FOUND;
    }
  }
  unsigned int bde_removeAll() const { return this->removeAll(); }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool bde_exists(F0 &&ltK, F1 &&eqK, const K key0) const {
    unsigned int lvl = stm::readTVar(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, key0, lvl);
  }
  bool bde_isEmpty() const { return this->isEmpty(); }
  unsigned int bde_length() const { return this->length(); }
  template <MapsTo<bool, K, K> F0>
  bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>>
  bde_previous(F0 &&eqK, const bsl::shared_ptr<SkipNode<K, V>> pair) const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> prevOpt =
        this->previous(eqK, pair);
    if (prevOpt.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *prevOpt;
      return bsl::make_pair(
          SkipList<int, int>::e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>());
    }
  }
  template <MapsTo<bool, K, K> F0>
  bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>>
  bde_findLowerBound(F0 &&ltK, const K key0) const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> result =
        this->findLowerBound(ltK, key0);
    if (result.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *result;
      return bsl::make_pair(
          SkipList<int, int>::e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>());
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bsl::pair<unsigned int, bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>>
  bde_findUpperBound(F0 &&ltK, F1 &&eqK, const K key0) const {
    bsl::optional<bsl::shared_ptr<SkipNode<K, V>>> result =
        this->findUpperBound(ltK, eqK, key0);
    if (result.has_value()) {
      bsl::shared_ptr<SkipNode<K, V>> node = *result;
      return bsl::make_pair(
          SkipList<int, int>::e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<K, V>>>());
    }
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<SkipNode<T1, T2>>
  findPred_go(F0 &&ltK, const unsigned int fuel,
              const bsl::shared_ptr<SkipNode<T1, T2>> curr, const T1 target,
              const unsigned int level) {
    bsl::shared_ptr<SkipNode<T1, T2>> _result;
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        _result = _loop_curr;
        _continue = false;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[level]));
        if (nextOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
          if (ltK(next0->key, target)) {
            bsl::shared_ptr<SkipNode<T1, T2>> _next_curr = next0;
            unsigned int _next_fuel = fuel_;
            _loop_curr = bsl::move(_next_curr);
            _loop_fuel = bsl::move(_next_fuel);
          } else {
            _result = _loop_curr;
            _continue = false;
          }
        } else {
          _result = _loop_curr;
          _continue = false;
        }
      }
    }
    return _result;
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<SkipNode<T1, T2>>
  findPred(F0 &&ltK, const bsl::shared_ptr<SkipNode<T1, T2>> curr,
           const T1 target, const unsigned int level) {
    return SkipList<int, int>::template findPred_go<T1, T2>(ltK, 10000u, curr,
                                                            target, level);
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static SkipPath<T1, T2>
  findPath_aux(F0 &&ltK, const bsl::shared_ptr<SkipNode<T1, T2>> curr,
               const T1 target, const unsigned int level,
               const SkipPath<T1, T2> path) {
    SkipPath<T1, T2> _result;
    unsigned int _loop_level = level;
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    bool _continue = true;
    while (_continue) {
      bsl::shared_ptr<SkipNode<T1, T2>> pred =
          SkipList<int, int>::template findPred<T1, T2>(ltK, _loop_curr, target,
                                                        _loop_level);
      path.set(_loop_level, pred);
      if (_loop_level <= 0) {
        _result = path;
        _continue = false;
      } else {
        unsigned int level_ = _loop_level - 1;
        unsigned int _next_level = level_;
        bsl::shared_ptr<SkipNode<T1, T2>> _next_curr = pred;
        _loop_level = bsl::move(_next_level);
        _loop_curr = bsl::move(_next_curr);
      }
    }
    return _result;
  }
  template <typename T1, typename T2>
  static void linkAtLevel(const bsl::shared_ptr<SkipNode<T1, T2>> pred,
                          const bsl::shared_ptr<SkipNode<T1, T2>> newNode,
                          const unsigned int level) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> oldNext = ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred->forward[level]));
    stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level],
        opt_to_ptr(
            bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(newNode)));
    stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(newNode->forward[level],
                                                      opt_to_ptr(oldNext));
    return;
  }
  template <typename T1, typename T2>
  static void linkNode_aux(const SkipPath<T1, T2> path,
                           const bsl::shared_ptr<SkipNode<T1, T2>>,
                           const bsl::shared_ptr<SkipNode<T1, T2>> newNode,
                           const unsigned int level) {
    unsigned int _loop_level = level;
    while (true) {
      bsl::shared_ptr<SkipNode<T1, T2>> pred = path.get(_loop_level);
      SkipList<int, int>::template linkAtLevel<T1, T2>(pred, newNode,
                                                       _loop_level);
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
  static void extendPath_aux(const SkipPath<T1, T2> path,
                             const bsl::shared_ptr<SkipNode<T1, T2>> head,
                             const unsigned int level,
                             const unsigned int maxLevel) {
    unsigned int _loop_level = level;
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
  static void extendPath(const SkipPath<T1, T2> path,
                         const bsl::shared_ptr<SkipNode<T1, T2>> head,
                         const unsigned int needed,
                         const unsigned int currentMax) {
    if (needed <= (currentMax + 1)) {
      return;
    } else {
      SkipList<int, int>::template extendPath_aux<T1, T2>(
          path, head, (((needed - 1u) > needed ? 0 : (needed - 1u))),
          (currentMax + 1u));
      return;
    }
  }
  template <typename T1, typename T2>
  static void linkNode(const SkipPath<T1, T2> path,
                       const bsl::shared_ptr<SkipNode<T1, T2>> head,
                       const bsl::shared_ptr<SkipNode<T1, T2>> newNode) {
    unsigned int lvl = newNode->level;
    SkipList<int, int>::template linkNode_aux<T1, T2>(path, head, newNode, lvl);
    return;
  }
  template <typename T1, typename T2>
  static void unlinkAtLevel(const bsl::shared_ptr<SkipNode<T1, T2>> pred,
                            const bsl::shared_ptr<SkipNode<T1, T2>> target,
                            const unsigned int level) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> targetNext =
        ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
            target->forward[level]));
    stm::writeTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pred->forward[level],
                                                      opt_to_ptr(targetNext));
    return;
  }
  template <typename T1, typename T2>
  static void unlinkNode_aux(const SkipPath<T1, T2> path,
                             const bsl::shared_ptr<SkipNode<T1, T2>> target,
                             const unsigned int level) {
    unsigned int _loop_level = level;
    while (true) {
      bsl::shared_ptr<SkipNode<T1, T2>> pred = path.get(_loop_level);
      SkipList<int, int>::template unlinkAtLevel<T1, T2>(pred, target,
                                                         _loop_level);
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
  static void unlinkNode(const SkipPath<T1, T2> path,
                         const bsl::shared_ptr<SkipNode<T1, T2>> target) {
    unsigned int lvl = target->level;
    SkipList<int, int>::template unlinkNode_aux<T1, T2>(path, target, lvl);
    return;
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static bool findKey_aux(F0 &&ltK, F1 &&eqK,
                          const bsl::shared_ptr<SkipNode<T1, T2>> curr,
                          const T1 target, const unsigned int level) {
    bool _result;
    unsigned int _loop_level = level;
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    bool _continue = true;
    while (_continue) {
      bsl::shared_ptr<SkipNode<T1, T2>> pred =
          SkipList<int, int>::template findPred<T1, T2>(ltK, _loop_curr, target,
                                                        _loop_level);
      if (_loop_level <= 0) {
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                pred->forward[0u]));
        if (nextOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
          _result = eqK(node->key, target);
          _continue = false;
        } else {
          _result = false;
          _continue = false;
        }
      } else {
        unsigned int level_ = _loop_level - 1;
        unsigned int _next_level = level_;
        bsl::shared_ptr<SkipNode<T1, T2>> _next_curr = pred;
        _loop_level = bsl::move(_next_level);
        _loop_curr = bsl::move(_next_curr);
      }
    }
    return _result;
  }
  template <typename T1, typename T2>
  static unsigned int
  length_aux(const unsigned int fuel,
             const bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> node,
             const unsigned int acc) {
    unsigned int _result;
    unsigned int _loop_acc = acc;
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> _loop_node = node;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        _result = _loop_acc;
        _continue = false;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        if (_loop_node.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> n = *_loop_node;
          bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
              stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(n->forward[0u]));
          unsigned int _next_acc = (_loop_acc + 1);
          bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> _next_node = nextOpt;
          unsigned int _next_fuel = fuel_;
          _loop_acc = bsl::move(_next_acc);
          _loop_node = bsl::move(_next_node);
          _loop_fuel = bsl::move(_next_fuel);
        } else {
          _result = _loop_acc;
          _continue = false;
        }
      }
    }
    return _result;
  }
  template <typename T1, typename T2>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  findLast_aux(const unsigned int fuel,
               const bsl::shared_ptr<SkipNode<T1, T2>> curr) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> _result;
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        _result =
            bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(_loop_curr);
        _continue = false;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[0u]));
        if (nextOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
          bsl::shared_ptr<SkipNode<T1, T2>> _next_curr = next0;
          unsigned int _next_fuel = fuel_;
          _loop_curr = bsl::move(_next_curr);
          _loop_fuel = bsl::move(_next_fuel);
        } else {
          _result =
              bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(_loop_curr);
          _continue = false;
        }
      }
    }
    return _result;
  }
  template <typename T1, typename T2>
  static void unlinkFirstFromHead(const bsl::shared_ptr<SkipNode<T1, T2>> head,
                                  const bsl::shared_ptr<SkipNode<T1, T2>> node,
                                  const unsigned int lvl) {
    unsigned int _loop_lvl = lvl;
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
  static void
  unlinkNodeAtAllLevels(const bsl::shared_ptr<SkipNode<T1, T2>> head,
                        const bsl::shared_ptr<SkipNode<T1, T2>> node,
                        const unsigned int lvl) {
    unsigned int _loop_lvl = lvl;
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
  static unsigned int
  removeAll_aux(const unsigned int fuel,
                const bsl::shared_ptr<SkipNode<T1, T2>> head,
                const unsigned int acc) {
    if (fuel <= 0) {
      return acc;
    } else {
      unsigned int fuel_ = fuel - 1;
      bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> firstOpt = ptr_to_opt(
          stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(head->forward[0u]));
      if (firstOpt.has_value()) {
        bsl::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
        SkipList<int, int>::template unlinkNodeAtAllLevels<T1, T2>(head, node,
                                                                   node->level);
        return SkipList<int, int>::template removeAll_aux<T1, T2>(fuel_, head,
                                                                  (acc + 1));
      } else {
        return acc;
      }
    }
  }
  template <typename T1, typename T2>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  next(const bsl::shared_ptr<SkipNode<T1, T2>> pair) {
    return ptr_to_opt(
        stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(pair->forward[0u]));
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>
  findPrev_aux(F0 &&eqK, const unsigned int fuel,
               const bsl::shared_ptr<SkipNode<T1, T2>> curr,
               const bsl::shared_ptr<SkipNode<T1, T2>> _x, const T1 target) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> _result;
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_x = _x;
    bsl::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        _result = bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
        _continue = false;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<bsl::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[0u]));
        if (nextOpt.has_value()) {
          bsl::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
          if (eqK(next0->key, target)) {
            _result = bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr);
            _continue = false;
          } else {
            bsl::shared_ptr<SkipNode<T1, T2>> _next_x = _loop_curr;
            bsl::shared_ptr<SkipNode<T1, T2>> _next_curr = next0;
            unsigned int _next_fuel = fuel_;
            _loop_x = bsl::move(_next_x);
            _loop_curr = bsl::move(_next_curr);
            _loop_fuel = bsl::move(_next_fuel);
          }
        } else {
          _result = bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>();
          _continue = false;
        }
      }
    }
    return _result;
  }
  template <typename T1, typename T2>
  static T1 key(const bsl::shared_ptr<SkipNode<T1, T2>> _x0) {
    return _x0->key;
  }
  template <typename T1, typename T2>
  static T2 data(const bsl::shared_ptr<SkipNode<T1, T2>> _x0) {
    return stm::readTVar<T2>(_x0->value);
  }
  static inline const unsigned int e_SUCCESS = 0u;
  static inline const unsigned int e_NOT_FOUND = 1u;
  static inline const unsigned int e_DUPLICATE = 2u;
  static inline const unsigned int e_INVALID = 3u;
  template <typename T1, typename T2>
  static bsl::pair<unsigned int,
                   bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>>
  bde_next(const bsl::shared_ptr<SkipNode<T1, T2>> pair) {
    bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>> nextOpt =
        SkipList<int, int>::template next<T1, T2>(pair);
    if (nextOpt.has_value()) {
      bsl::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      return bsl::make_pair(
          SkipList<int, int>::e_SUCCESS,
          bsl::make_optional<bsl::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return bsl::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            bsl::optional<bsl::shared_ptr<SkipNode<T1, T2>>>());
    }
  }
  template <typename T1, typename T2>
  static bsl::shared_ptr<SkipList<T1, T2>> create(const T1 dummyKey,
                                                  const T2 dummyVal) {
    bsl::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal, (((16u - 1u) > 16u ? 0 : (16u - 1u))));
    stm::TVar<unsigned int> lvlTV = stm::newTVar(0u);
    stm::TVar<unsigned int> lenTV = stm::newTVar(0u);
    return bsl::make_shared<SkipList<T1, T2>>(
        SkipList<T1, T2>{headNode, 16u, lvlTV, lenTV});
  }
  template <typename T1, typename T2>
  static bsl::shared_ptr<SkipList<T1, T2>> createIO(const T1 dummyKey,
                                                    const T2 dummyVal) {
    return stm::atomically([&] {
      return SkipList<int, int>::template create<T1, T2>(dummyKey, dummyVal);
    });
  }
};

#endif // INCLUDED_SKIPLIST_BDE
