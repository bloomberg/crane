#ifndef INCLUDED_SKIPLIST
#define INCLUDED_SKIPLIST

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <skipnode.h>
#include <stm_adapter.h>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename K, typename V> struct SkipList {
  std::shared_ptr<SkipNode<K, V>> slHead;
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
  std::optional<V> lookup(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *nextOpt;
      if (eqK(node->key, k)) {
        V v = stm::readTVar<V>(node->value);
        return std::make_optional<V>(v);
      } else {
        return std::optional<V>();
      }
    } else {
      return std::optional<V>();
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::monostate insert(F0 &&ltK, F1 &&eqK, const K k, const V v,
                        const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &existing = *nextOpt;
      if (eqK(existing->key, k)) {
        stm::writeTVar<V>(existing->value, v);
        return std::monostate{};
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
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
        unsigned int len = stm::readTVar(this->SkipList::slLength);
        stm::writeTVar(this->SkipList::slLength, (len + 1));
        return std::monostate{};
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
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
      unsigned int len = stm::readTVar(this->SkipList::slLength);
      stm::writeTVar(this->SkipList::slLength, (len + 1));
      return std::monostate{};
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::monostate remove(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *nextOpt;
      if (eqK(node->key, k)) {
        unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (node->level + 1), curLvl);
        SkipList<int, int>::template unlinkNode<K, V>(path, node);
        unsigned int len = stm::readTVar(this->SkipList::slLength);
        stm::writeTVar(this->SkipList::slLength,
                       (((len - 1u) > len ? 0 : (len - 1u))));
        return std::monostate{};
      } else {
        return std::monostate{};
      }
    } else {
      return std::monostate{};
    }
  }

  std::optional<std::pair<K, V>> minimum() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *firstOpt;
      V v = stm::readTVar<V>(node->value);
      return std::make_optional<std::pair<K, V>>(std::make_pair(node->key, v));
    } else {
      return std::optional<std::pair<K, V>>();
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
    unsigned int len = stm::readTVar(this->SkipList::slLength);
    return len == 0u;
  }

  unsigned int length() const {
    return stm::readTVar(this->SkipList::slLength);
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool exists_(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = stm::readTVar(this->SkipList::slLevel);
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }

  std::optional<std::shared_ptr<SkipNode<K, V>>> front() const {
    return ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
        this->SkipList::slHead->forward[0u]));
  }

  std::optional<std::shared_ptr<SkipNode<K, V>>> back() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &first = *firstOpt;
      return SkipList<int, int>::template findLast_aux<K, V>(10000u, first);
    } else {
      return std::optional<std::shared_ptr<SkipNode<K, V>>>();
    }
  }

  std::optional<std::pair<K, V>> popFront() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level);
      unsigned int len = stm::readTVar(this->SkipList::slLength);
      stm::writeTVar(this->SkipList::slLength,
                     (((len - 1u) > len ? 0 : (len - 1u))));
      V v = stm::readTVar<V>(node->value);
      return std::make_optional<std::pair<K, V>>(std::make_pair(node->key, v));
    } else {
      return std::optional<std::pair<K, V>>();
    }
  }

  unsigned int removeAll() const {
    unsigned int count = SkipList<int, int>::template removeAll_aux<K, V>(
        10000u, this->SkipList::slHead, 0u);
    stm::writeTVar(this->SkipList::slLength, 0u);
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
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &existing = *nextOpt;
      if (eqK(existing->key, k)) {
        stm::writeTVar<V>(existing->value, v);
        return std::monostate{};
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
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
        unsigned int len = stm::readTVar(this->SkipList::slLength);
        stm::writeTVar(this->SkipList::slLength, (len + 1));
        return std::monostate{};
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
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
      unsigned int len = stm::readTVar(this->SkipList::slLength);
      stm::writeTVar(this->SkipList::slLength, (len + 1));
      return std::monostate{};
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool addUnique(F0 &&ltK, F1 &&eqK, const K k, const V v,
                 const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &existing = *nextOpt;
      if (eqK(existing->key, k)) {
        return false;
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
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
        unsigned int len = stm::readTVar(this->SkipList::slLength);
        stm::writeTVar(this->SkipList::slLength, (len + 1));
        return true;
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
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
      unsigned int len = stm::readTVar(this->SkipList::slLength);
      stm::writeTVar(this->SkipList::slLength, (len + 1));
      return true;
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::optional<std::shared_ptr<SkipNode<K, V>>> find(F0 &&ltK, F1 &&eqK,
                                                      const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *nextOpt;
      if (eqK(node->key, k)) {
        return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node);
      } else {
        return std::optional<std::shared_ptr<SkipNode<K, V>>>();
      }
    } else {
      return std::optional<std::shared_ptr<SkipNode<K, V>>>();
    }
  }

  template <MapsTo<bool, K, K> F0>
  std::optional<std::shared_ptr<SkipNode<K, V>>>
  previous(F0 &&eqK, const std::shared_ptr<SkipNode<K, V>> pair) const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &first = *firstOpt;
      if (eqK(first->key, pair->key)) {
        return std::optional<std::shared_ptr<SkipNode<K, V>>>();
      } else {
        return SkipList<int, int>::template findPrev_aux<K, V>(
            eqK, 10000u, first, this->SkipList::slHead, pair->key);
      }
    } else {
      return std::optional<std::shared_ptr<SkipNode<K, V>>>();
    }
  }

  template <MapsTo<bool, K, K> F0>
  std::optional<std::shared_ptr<SkipNode<K, V>>>
  findLowerBound(F0 &&ltK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *nextOpt;
      return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node);
    } else {
      return std::optional<std::shared_ptr<SkipNode<K, V>>>();
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::optional<std::shared_ptr<SkipNode<K, V>>>
  findUpperBound(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *nextOpt;
      if (eqK(node->key, k)) {
        return ptr_to_opt(
            stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(node->forward[0u]));
      } else {
        return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node);
      }
    } else {
      return std::optional<std::shared_ptr<SkipNode<K, V>>>();
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool removePair(F0 &&ltK, F1 &&eqK,
                  const std::shared_ptr<SkipNode<K, V>> pair) const {
    K k = pair->key;
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *nextOpt;
      if (eqK(node->key, k)) {
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (node->level + 1), curLvl);
        SkipList<int, int>::template unlinkNode<K, V>(path, node);
        unsigned int len = stm::readTVar(this->SkipList::slLength);
        stm::writeTVar(this->SkipList::slLength,
                       (((len - 1u) > len ? 0 : (len - 1u))));
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::pair<std::shared_ptr<SkipNode<K, V>>, bool>
  bde_add(F0 &&ltK, F1 &&eqK, const K key0, const V data0,
          const unsigned int level) const {
    SkipPath<K, V> path = this->findPath(ltK, key0);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (level + 1), curLvl);
    std::optional<std::shared_ptr<SkipNode<K, V>>> curFront =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    bool isNewFront;
    if (curFront.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &existing = *nextOpt;
      if (eqK(existing->key, key0)) {
        stm::writeTVar<V>(existing->value, data0);
        return std::make_pair(existing, false);
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
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
        unsigned int len = stm::readTVar(this->SkipList::slLength);
        stm::writeTVar(this->SkipList::slLength, (len + 1));
        return std::make_pair(newN, isNewFront);
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
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
      unsigned int len = stm::readTVar(this->SkipList::slLength);
      stm::writeTVar(this->SkipList::slLength, (len + 1));
      return std::make_pair(newN, isNewFront);
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::pair<
      std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>,
      bool>
  bde_addUnique(F0 &&ltK, F1 &&eqK, const K key0, const V data0,
                const unsigned int level) const {
    SkipPath<K, V> path = this->findPath(ltK, key0);
    unsigned int curLvl = stm::readTVar(this->SkipList::slLevel);
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (level + 1), curLvl);
    std::optional<std::shared_ptr<SkipNode<K, V>>> curFront =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    bool isNewFront;
    if (curFront.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &existing = *nextOpt;
      if (eqK(existing->key, key0)) {
        return std::make_pair(
            std::make_pair(SkipList<int, int>::e_DUPLICATE,
                           std::optional<std::shared_ptr<SkipNode<K, V>>>()),
            false);
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
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
        unsigned int len = stm::readTVar(this->SkipList::slLength);
        stm::writeTVar(this->SkipList::slLength, (len + 1));
        return std::make_pair(
            std::make_pair(
                SkipList<int, int>::e_SUCCESS,
                std::make_optional<std::shared_ptr<SkipNode<K, V>>>(newN)),
            isNewFront);
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
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
      unsigned int len = stm::readTVar(this->SkipList::slLength);
      stm::writeTVar(this->SkipList::slLength, (len + 1));
      return std::make_pair(
          std::make_pair(
              SkipList<int, int>::e_SUCCESS,
              std::make_optional<std::shared_ptr<SkipNode<K, V>>>(newN)),
          isNewFront);
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_find(F0 &&ltK, F1 &&eqK, const K key0) const {
    SkipPath<K, V> path = this->findPath(ltK, key0);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0u);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0u]));
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *nextOpt;
      if (eqK(node->key, key0)) {
        return std::make_pair(
            SkipList<int, int>::e_SUCCESS,
            std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
      } else {
        return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                              std::optional<std::shared_ptr<SkipNode<K, V>>>());
      }
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<K, V>>>());
    }
  }

  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_front() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> frontOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (frontOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *frontOpt;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<K, V>>>());
    }
  }

  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_back() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> backOpt = this->back();
    if (backOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *backOpt;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<K, V>>>());
    }
  }

  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_popFront() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0u]));
    if (firstOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level);
      unsigned int len = stm::readTVar(this->SkipList::slLength);
      stm::writeTVar(this->SkipList::slLength,
                     (((len - 1u) > len ? 0 : (len - 1u))));
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<K, V>>>());
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  unsigned int bde_remove(F0 &&ltK, F1 &&eqK,
                          const std::shared_ptr<SkipNode<K, V>> pair) const {
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
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_previous(F0 &&eqK, const std::shared_ptr<SkipNode<K, V>> pair) const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> prevOpt =
        this->previous(eqK, pair);
    if (prevOpt.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *prevOpt;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<K, V>>>());
    }
  }

  template <MapsTo<bool, K, K> F0>
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_findLowerBound(F0 &&ltK, const K key0) const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> result =
        this->findLowerBound(ltK, key0);
    if (result.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *result;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<K, V>>>());
    }
  }

  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_findUpperBound(F0 &&ltK, F1 &&eqK, const K key0) const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> result =
        this->findUpperBound(ltK, eqK, key0);
    if (result.has_value()) {
      const std::shared_ptr<SkipNode<K, V>> &node = *result;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<K, V>>>());
    }
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<SkipNode<T1, T2>>
  findPred_go(F0 &&ltK, const unsigned int fuel,
              const std::shared_ptr<SkipNode<T1, T2>> curr, const T1 target,
              const unsigned int level) {
    std::shared_ptr<SkipNode<T1, T2>> _result;
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        _result = _loop_curr;
        _continue = false;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[level]));
        if (nextOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &next0 = *nextOpt;
          if (ltK(next0->key, target)) {
            std::shared_ptr<SkipNode<T1, T2>> _next_curr = next0;
            unsigned int _next_fuel = fuel_;
            _loop_curr = std::move(_next_curr);
            _loop_fuel = std::move(_next_fuel);
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
  static std::shared_ptr<SkipNode<T1, T2>>
  findPred(F0 &&ltK, const std::shared_ptr<SkipNode<T1, T2>> curr,
           const T1 target, const unsigned int level) {
    return SkipList<int, int>::template findPred_go<T1, T2>(ltK, 10000u, curr,
                                                            target, level);
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static SkipPath<T1, T2>
  findPath_aux(F0 &&ltK, const std::shared_ptr<SkipNode<T1, T2>> curr,
               const T1 target, const unsigned int level,
               const SkipPath<T1, T2> path) {
    SkipPath<T1, T2> _result;
    unsigned int _loop_level = level;
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    bool _continue = true;
    while (_continue) {
      std::shared_ptr<SkipNode<T1, T2>> pred =
          SkipList<int, int>::template findPred<T1, T2>(ltK, _loop_curr, target,
                                                        _loop_level);
      path.set(_loop_level, pred);
      if (_loop_level <= 0) {
        _result = path;
        _continue = false;
      } else {
        unsigned int level_ = _loop_level - 1;
        unsigned int _next_level = level_;
        std::shared_ptr<SkipNode<T1, T2>> _next_curr = pred;
        _loop_level = std::move(_next_level);
        _loop_curr = std::move(_next_curr);
      }
    }
    return _result;
  }

  template <typename T1, typename T2>
  static void linkAtLevel(const std::shared_ptr<SkipNode<T1, T2>> pred,
                          const std::shared_ptr<SkipNode<T1, T2>> newNode,
                          const unsigned int level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> oldNext = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(pred->forward[level]));
    stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level],
        opt_to_ptr(
            std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(newNode)));
    stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(newNode->forward[level],
                                                      opt_to_ptr(oldNext));
    return;
  }

  template <typename T1, typename T2>
  static void linkNode_aux(const SkipPath<T1, T2> path,
                           const std::shared_ptr<SkipNode<T1, T2>>,
                           const std::shared_ptr<SkipNode<T1, T2>> newNode,
                           const unsigned int level) {
    unsigned int _loop_level = level;
    while (true) {
      std::shared_ptr<SkipNode<T1, T2>> pred = path.get(_loop_level);
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
                             const std::shared_ptr<SkipNode<T1, T2>> head,
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
                         const std::shared_ptr<SkipNode<T1, T2>> head,
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
                       const std::shared_ptr<SkipNode<T1, T2>> head,
                       const std::shared_ptr<SkipNode<T1, T2>> newNode) {
    unsigned int lvl = newNode->level;
    SkipList<int, int>::template linkNode_aux<T1, T2>(path, head, newNode, lvl);
    return;
  }

  template <typename T1, typename T2>
  static void unlinkAtLevel(const std::shared_ptr<SkipNode<T1, T2>> pred,
                            const std::shared_ptr<SkipNode<T1, T2>> target,
                            const unsigned int level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> targetNext =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
            target->forward[level]));
    stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(pred->forward[level],
                                                      opt_to_ptr(targetNext));
    return;
  }

  template <typename T1, typename T2>
  static void unlinkNode_aux(const SkipPath<T1, T2> path,
                             const std::shared_ptr<SkipNode<T1, T2>> target,
                             const unsigned int level) {
    unsigned int _loop_level = level;
    while (true) {
      std::shared_ptr<SkipNode<T1, T2>> pred = path.get(_loop_level);
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
                         const std::shared_ptr<SkipNode<T1, T2>> target) {
    unsigned int lvl = target->level;
    SkipList<int, int>::template unlinkNode_aux<T1, T2>(path, target, lvl);
    return;
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static bool findKey_aux(F0 &&ltK, F1 &&eqK,
                          const std::shared_ptr<SkipNode<T1, T2>> curr,
                          const T1 target, const unsigned int level) {
    bool _result;
    unsigned int _loop_level = level;
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    bool _continue = true;
    while (_continue) {
      std::shared_ptr<SkipNode<T1, T2>> pred =
          SkipList<int, int>::template findPred<T1, T2>(ltK, _loop_curr, target,
                                                        _loop_level);
      if (_loop_level <= 0) {
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                pred->forward[0u]));
        if (nextOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &node = *nextOpt;
          _result = eqK(node->key, target);
          _continue = false;
        } else {
          _result = false;
          _continue = false;
        }
      } else {
        unsigned int level_ = _loop_level - 1;
        unsigned int _next_level = level_;
        std::shared_ptr<SkipNode<T1, T2>> _next_curr = pred;
        _loop_level = std::move(_next_level);
        _loop_curr = std::move(_next_curr);
      }
    }
    return _result;
  }

  template <typename T1, typename T2>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findLast_aux(const unsigned int fuel,
               const std::shared_ptr<SkipNode<T1, T2>> curr) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> _result;
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        _result =
            std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(_loop_curr);
        _continue = false;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[0u]));
        if (nextOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &next0 = *nextOpt;
          std::shared_ptr<SkipNode<T1, T2>> _next_curr = next0;
          unsigned int _next_fuel = fuel_;
          _loop_curr = std::move(_next_curr);
          _loop_fuel = std::move(_next_fuel);
        } else {
          _result =
              std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(_loop_curr);
          _continue = false;
        }
      }
    }
    return _result;
  }

  template <typename T1, typename T2>
  static void unlinkFirstFromHead(const std::shared_ptr<SkipNode<T1, T2>> head,
                                  const std::shared_ptr<SkipNode<T1, T2>> node,
                                  const unsigned int lvl) {
    unsigned int _loop_lvl = lvl;
    while (true) {
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
          ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
              node->forward[_loop_lvl]));
      stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
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
  unlinkNodeAtAllLevels(const std::shared_ptr<SkipNode<T1, T2>> head,
                        const std::shared_ptr<SkipNode<T1, T2>> node,
                        const unsigned int lvl) {
    unsigned int _loop_lvl = lvl;
    while (true) {
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
          ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
              node->forward[_loop_lvl]));
      stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
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
                const std::shared_ptr<SkipNode<T1, T2>> head,
                const unsigned int acc) {
    if (fuel <= 0) {
      return acc;
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt = ptr_to_opt(
          stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(head->forward[0u]));
      if (firstOpt.has_value()) {
        const std::shared_ptr<SkipNode<T1, T2>> &node = *firstOpt;
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
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  next(const std::shared_ptr<SkipNode<T1, T2>> pair) {
    return ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(pair->forward[0u]));
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findPrev_aux(F0 &&eqK, const unsigned int fuel,
               const std::shared_ptr<SkipNode<T1, T2>> curr,
               const std::shared_ptr<SkipNode<T1, T2>> _x, const T1 target) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> _result;
    std::shared_ptr<SkipNode<T1, T2>> _loop_x = _x;
    std::shared_ptr<SkipNode<T1, T2>> _loop_curr = curr;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        _result = std::optional<std::shared_ptr<SkipNode<T1, T2>>>();
        _continue = false;
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr->forward[0u]));
        if (nextOpt.has_value()) {
          const std::shared_ptr<SkipNode<T1, T2>> &next0 = *nextOpt;
          if (eqK(next0->key, target)) {
            _result = std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(
                _loop_curr);
            _continue = false;
          } else {
            std::shared_ptr<SkipNode<T1, T2>> _next_x = _loop_curr;
            std::shared_ptr<SkipNode<T1, T2>> _next_curr = next0;
            unsigned int _next_fuel = fuel_;
            _loop_x = std::move(_next_x);
            _loop_curr = std::move(_next_curr);
            _loop_fuel = std::move(_next_fuel);
          }
        } else {
          _result = std::optional<std::shared_ptr<SkipNode<T1, T2>>>();
          _continue = false;
        }
      }
    }
    return _result;
  }

  template <typename T1, typename T2>
  static T1 key(const std::shared_ptr<SkipNode<T1, T2>> _x0) {
    return _x0->key;
  }

  template <typename T1, typename T2>
  static T2 data(const std::shared_ptr<SkipNode<T1, T2>> _x0) {
    return stm::readTVar<T2>(_x0->value);
  }

  static inline const unsigned int e_SUCCESS = 0u;
  static inline const unsigned int e_NOT_FOUND = 1u;
  static inline const unsigned int e_DUPLICATE = 2u;
  static inline const unsigned int e_INVALID = 3u;

  template <typename T1, typename T2>
  static std::pair<unsigned int,
                   std::optional<std::shared_ptr<SkipNode<T1, T2>>>>
  bde_next(const std::shared_ptr<SkipNode<T1, T2>> pair) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
        SkipList<int, int>::template next<T1, T2>(pair);
    if (nextOpt.has_value()) {
      const std::shared_ptr<SkipNode<T1, T2>> &node = *nextOpt;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                            std::optional<std::shared_ptr<SkipNode<T1, T2>>>());
    }
  }

  template <typename T1, typename T2>
  static std::shared_ptr<SkipList<T1, T2>> create(const T1 dummyKey,
                                                  const T2 dummyVal) {
    std::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal, (((16u - 1u) > 16u ? 0 : (16u - 1u))));
    stm::TVar<unsigned int> lvlTV = stm::newTVar(0u);
    stm::TVar<unsigned int> lenTV = stm::newTVar(0u);
    return std::make_shared<SkipList<T1, T2>>(
        SkipList<T1, T2>{headNode, 16u, lvlTV, lenTV});
  }

  template <typename T1, typename T2>
  static std::shared_ptr<SkipList<T1, T2>> createIO(const T1 dummyKey,
                                                    const T2 dummyVal) {
    return stm::atomically([&] {
      return SkipList<int, int>::template create<T1, T2>(dummyKey, dummyVal);
    });
  }
};

struct skiplist_test {
  __attribute__((pure)) static bool nat_lt(const unsigned int _x0,
                                           const unsigned int _x1);
  __attribute__((pure)) static bool nat_eq(const unsigned int _x0,
                                           const unsigned int _x1);
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
  static unsigned int run_tests();
};

#endif // INCLUDED_SKIPLIST
