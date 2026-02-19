#include <algorithm>
#include <any>
#include <cassert>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <skipnode.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  static bool eqb(const unsigned int n, const unsigned int m);

  static bool leb(const unsigned int n, const unsigned int m);

  static bool ltb(const unsigned int n, const unsigned int m);
};

struct STM {};

struct TVar {};

template <typename K, typename V> struct SkipList {
  std::shared_ptr<SkipNode<K, V>> slHead;
  unsigned int slMaxLevel;
  std::shared_ptr<stm::TVar<unsigned int>> slLevel;
  std::shared_ptr<stm::TVar<unsigned int>> slLength;
  template <MapsTo<bool, K, K> F0>
  SkipPath<K, V> findPath(F0 &&ltK, const K target) const {
    unsigned int lvl = this->SkipList::slLevel->read();
    SkipPath<K, V> path = SkipPath<K, V>{};
    return SkipList<int, int>::template findPath_aux<K, V>(
        ltK, this->SkipList::slHead, target, lvl, path);
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::optional<V> lookup(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        V v = stm::readTVar<V>(node->value);
        return std::make_optional<V>(v);
      } else {
        return std::nullopt;
      }
    } else {
      return std::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  void insert(F0 &&ltK, F1 &&eqK, const K k, const V v,
              const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = this->SkipList::slLevel->read();
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        return stm::writeTVar<V>(existing->value, v);
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(k, v, newLevel);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&](void) {
          if (Nat::ltb(curLvl, newLevel)) {
            return this->SkipList::slLevel->write(newLevel);
          } else {
            return;
          }
        }();
        unsigned int len = this->SkipList::slLength->read();
        return this->SkipList::slLength->write((len + 1));
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&](void) {
        if (Nat::ltb(curLvl, newLevel)) {
          return this->SkipList::slLevel->write(newLevel);
        } else {
          return;
        }
      }();
      unsigned int len = this->SkipList::slLength->read();
      return this->SkipList::slLength->write((len + 1));
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  void remove(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        unsigned int curLvl = this->SkipList::slLevel->read();
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (node->level + 1), curLvl);
        SkipList<int, int>::template unlinkNode<K, V>(path, node);
        unsigned int len = this->SkipList::slLength->read();
        return this->SkipList::slLength->write(
            (((len - (0 + 1)) > len ? 0 : (len - (0 + 1)))));
      } else {
        return;
      }
    } else {
      return;
    }
  }
  std::optional<std::pair<K, V>> minimum() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0]));
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      V v = stm::readTVar<V>(node->value);
      return std::make_optional<std::pair<K, V>>(std::make_pair(node->key, v));
    } else {
      return std::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool memberFast(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = this->SkipList::slLevel->read();
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool member(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = this->SkipList::slLevel->read();
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  bool isEmpty() const {
    unsigned int len = this->SkipList::slLength->read();
    return Nat::eqb(len, 0);
  }
  unsigned int length() const { return this->SkipList::slLength->read(); }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool exists_(F0 &&ltK, F1 &&eqK, const K k) const {
    unsigned int lvl = this->SkipList::slLevel->read();
    return SkipList<int, int>::template findKey_aux<K, V>(
        ltK, eqK, this->SkipList::slHead, k, lvl);
  }
  std::optional<std::shared_ptr<SkipNode<K, V>>> front() const {
    return ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
        this->SkipList::slHead->forward[0]));
  }
  std::optional<std::shared_ptr<SkipNode<K, V>>> back() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0]));
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> first = *firstOpt;
      return SkipList<int, int>::template findLast_aux<K, V>(10000u, first);
    } else {
      return std::nullopt;
    }
  }
  std::optional<std::pair<K, V>> popFront() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0]));
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level,
          (((16u - (0 + 1)) > 16u ? 0 : (16u - (0 + 1)))));
      unsigned int len = this->SkipList::slLength->read();
      this->SkipList::slLength->write(
          (((len - (0 + 1)) > len ? 0 : (len - (0 + 1)))));
      V v = stm::readTVar<V>(node->value);
      return std::make_optional<std::pair<K, V>>(std::make_pair(node->key, v));
    } else {
      return std::nullopt;
    }
  }
  unsigned int removeAll() const {
    unsigned int count = SkipList<int, int>::template removeAll_aux<K, V>(
        10000u, this->SkipList::slHead,
        (((16u - (0 + 1)) > 16u ? 0 : (16u - (0 + 1)))), 0);
    this->SkipList::slLength->write(0);
    this->SkipList::slLevel->write(0);
    return count;
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  void add(F0 &&ltK, F1 &&eqK, const K k, const V v,
           const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = this->SkipList::slLevel->read();
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        return stm::writeTVar<V>(existing->value, v);
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(k, v, newLevel);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&](void) {
          if (Nat::ltb(curLvl, newLevel)) {
            return this->SkipList::slLevel->write(newLevel);
          } else {
            return;
          }
        }();
        unsigned int len = this->SkipList::slLength->read();
        return this->SkipList::slLength->write((len + 1));
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&](void) {
        if (Nat::ltb(curLvl, newLevel)) {
          return this->SkipList::slLevel->write(newLevel);
        } else {
          return;
        }
      }();
      unsigned int len = this->SkipList::slLength->read();
      return this->SkipList::slLength->write((len + 1));
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool addUnique(F0 &&ltK, F1 &&eqK, const K k, const V v,
                 const unsigned int newLevel) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = this->SkipList::slLevel->read();
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (newLevel + 1), curLvl);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, k)) {
        return false;
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(k, v, newLevel);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&](void) {
          if (Nat::ltb(curLvl, newLevel)) {
            return this->SkipList::slLevel->write(newLevel);
          } else {
            return;
          }
        }();
        unsigned int len = this->SkipList::slLength->read();
        this->SkipList::slLength->write((len + 1));
        return true;
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(k, v, newLevel);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&](void) {
        if (Nat::ltb(curLvl, newLevel)) {
          return this->SkipList::slLevel->write(newLevel);
        } else {
          return;
        }
      }();
      unsigned int len = this->SkipList::slLength->read();
      this->SkipList::slLength->write((len + 1));
      return true;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::optional<std::shared_ptr<SkipNode<K, V>>> find(F0 &&ltK, F1 &&eqK,
                                                      const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node);
      } else {
        return std::nullopt;
      }
    } else {
      return std::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0>
  std::optional<std::shared_ptr<SkipNode<K, V>>>
  previous(F0 &&eqK, const std::shared_ptr<SkipNode<K, V>> pair) const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0]));
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> first = *firstOpt;
      if (eqK(first->key, pair->key)) {
        return std::nullopt;
      } else {
        return SkipList<int, int>::template findPrev_aux<K, V>(
            eqK, 10000u, first, this->SkipList::slHead, pair->key);
      }
    } else {
      return std::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0>
  std::optional<std::shared_ptr<SkipNode<K, V>>>
  findLowerBound(F0 &&ltK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node);
    } else {
      return std::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::optional<std::shared_ptr<SkipNode<K, V>>>
  findUpperBound(F0 &&ltK, F1 &&eqK, const K k) const {
    SkipPath<K, V> path = this->findPath(ltK, k);
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        return ptr_to_opt(
            stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(node->forward[0]));
      } else {
        return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node);
      }
    } else {
      return std::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool removePair(F0 &&ltK, F1 &&eqK,
                  const std::shared_ptr<SkipNode<K, V>> pair) const {
    K k = pair->key;
    SkipPath<K, V> path = this->findPath(ltK, k);
    unsigned int curLvl = this->SkipList::slLevel->read();
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, k)) {
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (node->level + 1), curLvl);
        SkipList<int, int>::template unlinkNode<K, V>(path, node);
        unsigned int len = this->SkipList::slLength->read();
        this->SkipList::slLength->write(
            (((len - (0 + 1)) > len ? 0 : (len - (0 + 1)))));
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
    unsigned int curLvl = this->SkipList::slLevel->read();
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (level + 1), curLvl);
    std::optional<std::shared_ptr<SkipNode<K, V>>> curFront =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0]));
    bool isNewFront;
    if (curFront.has_value()) {
      std::shared_ptr<SkipNode<K, V>> frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, key0)) {
        stm::writeTVar<V>(existing->value, data0);
        return std::make_pair(existing, false);
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(key0, data0, level);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&](void) {
          if (Nat::ltb(curLvl, level)) {
            return this->SkipList::slLevel->write(level);
          } else {
            return;
          }
        }();
        unsigned int len = this->SkipList::slLength->read();
        this->SkipList::slLength->write((len + 1));
        return std::make_pair(newN, isNewFront);
      }
    } else {
      std::shared_ptr<SkipNode<K, V>> newN =
          SkipNode<K, V>::create(key0, data0, level);
      SkipList<int, int>::template linkNode<K, V>(path, this->SkipList::slHead,
                                                  newN);
      [&](void) {
        if (Nat::ltb(curLvl, level)) {
          return this->SkipList::slLevel->write(level);
        } else {
          return;
        }
      }();
      unsigned int len = this->SkipList::slLength->read();
      this->SkipList::slLength->write((len + 1));
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
    unsigned int curLvl = this->SkipList::slLevel->read();
    SkipList<int, int>::template extendPath<K, V>(path, this->SkipList::slHead,
                                                  (level + 1), curLvl);
    std::optional<std::shared_ptr<SkipNode<K, V>>> curFront =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0]));
    bool isNewFront;
    if (curFront.has_value()) {
      std::shared_ptr<SkipNode<K, V>> frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
      if (eqK(existing->key, key0)) {
        return std::make_pair(
            std::make_pair(SkipList<int, int>::e_DUPLICATE, std::nullopt),
            false);
      } else {
        std::shared_ptr<SkipNode<K, V>> newN =
            SkipNode<K, V>::create(key0, data0, level);
        SkipList<int, int>::template linkNode<K, V>(
            path, this->SkipList::slHead, newN);
        [&](void) {
          if (Nat::ltb(curLvl, level)) {
            return this->SkipList::slLevel->write(level);
          } else {
            return;
          }
        }();
        unsigned int len = this->SkipList::slLength->read();
        this->SkipList::slLength->write((len + 1));
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
      [&](void) {
        if (Nat::ltb(curLvl, level)) {
          return this->SkipList::slLevel->write(level);
        } else {
          return;
        }
      }();
      unsigned int len = this->SkipList::slLength->read();
      this->SkipList::slLength->write((len + 1));
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
    std::shared_ptr<SkipNode<K, V>> pred0 = path.get(0);
    std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(pred0->forward[0]));
    if (nextOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
      if (eqK(node->key, key0)) {
        return std::make_pair(
            SkipList<int, int>::e_SUCCESS,
            std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
      } else {
        return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
      }
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
    }
  }
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_front() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> frontOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0]));
    if (frontOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *frontOpt;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
    }
  }
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_back() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> backOpt = this->back();
    if (backOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *backOpt;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
    }
  }
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_popFront() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<K, V>>>(
            this->SkipList::slHead->forward[0]));
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level,
          (((16u - (0 + 1)) > 16u ? 0 : (16u - (0 + 1)))));
      unsigned int len = this->SkipList::slLength->read();
      this->SkipList::slLength->write(
          (((len - (0 + 1)) > len ? 0 : (len - (0 + 1)))));
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
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
    unsigned int lvl = this->SkipList::slLevel->read();
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
      std::shared_ptr<SkipNode<K, V>> node = *prevOpt;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
    }
  }
  template <MapsTo<bool, K, K> F0>
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_findLowerBound(F0 &&ltK, const K key0) const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> result =
        this->findLowerBound(ltK, key0);
    if (result.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *result;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_findUpperBound(F0 &&ltK, F1 &&eqK, const K key0) const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> result =
        this->findUpperBound(ltK, eqK, key0);
    if (result.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *result;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
    }
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<SkipNode<T1, T2>>
  findPred_go(F0 &&ltK, const unsigned int fuel,
              const std::shared_ptr<SkipNode<T1, T2>> curr, const T1 target,
              const unsigned int level) {
    if (fuel <= 0) {
      return curr;
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
          ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
              curr->forward[level]));
      if (nextOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        if (ltK(next0->key, target)) {
          return SkipList<int, int>::template findPred_go<T1, T2>(
              ltK, fuel_, next0, target, level);
        } else {
          return curr;
        }
      } else {
        return curr;
      }
    }
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
    std::shared_ptr<SkipNode<T1, T2>> pred =
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
  static void linkAtLevel(const std::shared_ptr<SkipNode<T1, T2>> pred,
                          const std::shared_ptr<SkipNode<T1, T2>> newNode,
                          const unsigned int level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> oldNext = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(pred->forward[level]));
    stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level],
        opt_to_ptr(
            std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(newNode)));
    return stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
        newNode->forward[level], opt_to_ptr(oldNext));
  }

  template <typename T1, typename T2>
  static void linkNode_aux(const SkipPath<T1, T2> path,
                           const std::shared_ptr<SkipNode<T1, T2>> head,
                           const std::shared_ptr<SkipNode<T1, T2>> newNode,
                           const unsigned int level) {
    std::shared_ptr<SkipNode<T1, T2>> pred = path.get(level);
    SkipList<int, int>::template linkAtLevel<T1, T2>(pred, newNode, level);
    if (level <= 0) {
      return;
    } else {
      unsigned int level_ = level - 1;
      return SkipList<int, int>::template linkNode_aux<T1, T2>(path, head,
                                                               newNode, level_);
    }
  }

  template <typename T1, typename T2>
  static void extendPath_aux(const SkipPath<T1, T2> path,
                             const std::shared_ptr<SkipNode<T1, T2>> head,
                             const unsigned int level,
                             const unsigned int maxLevel) {
    if (level <= 0) {
      return path.set(0, head);
    } else {
      unsigned int level_ = level - 1;
      path.set(level, head);
      if (Nat::leb(maxLevel, level_)) {
        return SkipList<int, int>::template extendPath_aux<T1, T2>(
            path, head, level_, maxLevel);
      } else {
        return;
      }
    }
  }

  template <typename T1, typename T2>
  static void extendPath(const SkipPath<T1, T2> path,
                         const std::shared_ptr<SkipNode<T1, T2>> head,
                         const unsigned int needed,
                         const unsigned int currentMax) {
    if (Nat::leb(needed, (currentMax + 1))) {
      return;
    } else {
      return SkipList<int, int>::template extendPath_aux<T1, T2>(
          path, head, (((needed - (0 + 1)) > needed ? 0 : (needed - (0 + 1)))),
          (currentMax + (0 + 1)));
    }
  }

  template <typename T1, typename T2>
  static void linkNode(const SkipPath<T1, T2> path,
                       const std::shared_ptr<SkipNode<T1, T2>> head,
                       const std::shared_ptr<SkipNode<T1, T2>> newNode) {
    unsigned int lvl = newNode->level;
    return SkipList<int, int>::template linkNode_aux<T1, T2>(path, head,
                                                             newNode, lvl);
  }

  template <typename T1, typename T2>
  static void unlinkAtLevel(const std::shared_ptr<SkipNode<T1, T2>> pred,
                            const std::shared_ptr<SkipNode<T1, T2>> target,
                            const unsigned int level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> targetNext =
        ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
            target->forward[level]));
    return stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
        pred->forward[level], opt_to_ptr(targetNext));
  }

  template <typename T1, typename T2>
  static void unlinkNode_aux(const SkipPath<T1, T2> path,
                             const std::shared_ptr<SkipNode<T1, T2>> target,
                             const unsigned int level) {
    std::shared_ptr<SkipNode<T1, T2>> pred = path.get(level);
    SkipList<int, int>::template unlinkAtLevel<T1, T2>(pred, target, level);
    if (level <= 0) {
      return;
    } else {
      unsigned int level_ = level - 1;
      return SkipList<int, int>::template unlinkNode_aux<T1, T2>(path, target,
                                                                 level_);
    }
  }

  template <typename T1, typename T2>
  static void unlinkNode(const SkipPath<T1, T2> path,
                         const std::shared_ptr<SkipNode<T1, T2>> target) {
    unsigned int lvl = target->level;
    return SkipList<int, int>::template unlinkNode_aux<T1, T2>(path, target,
                                                               lvl);
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static bool findKey_aux(F0 &&ltK, F1 &&eqK,
                          const std::shared_ptr<SkipNode<T1, T2>> curr,
                          const T1 target, const unsigned int level) {
    std::shared_ptr<SkipNode<T1, T2>> pred =
        SkipList<int, int>::template findPred<T1, T2>(ltK, curr, target, level);
    if (level <= 0) {
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
          stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(pred->forward[0]));
      if (nextOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
        return eqK(node->key, target);
      } else {
        return false;
      }
    } else {
      unsigned int level_ = level - 1;
      return SkipList<int, int>::template findKey_aux<T1, T2>(ltK, eqK, pred,
                                                              target, level_);
    }
  }

  template <typename T1, typename T2>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findLast_aux(const unsigned int fuel,
               const std::shared_ptr<SkipNode<T1, T2>> curr) {
    if (fuel <= 0) {
      return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(curr);
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
          stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(curr->forward[0]));
      if (nextOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        return SkipList<int, int>::template findLast_aux<T1, T2>(fuel_, next0);
      } else {
        return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(curr);
      }
    }
  }

  template <typename T1, typename T2>
  static void unlinkFirstFromHead(const std::shared_ptr<SkipNode<T1, T2>> head,
                                  const std::shared_ptr<SkipNode<T1, T2>> node,
                                  const unsigned int nodeLevel,
                                  const unsigned int lvl) {
    if (lvl <= 0) {
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext = ptr_to_opt(
          stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(node->forward[0]));
      return stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
          head->forward[0], opt_to_ptr(nodeNext));
    } else {
      unsigned int lvl_ = lvl - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> headNext = ptr_to_opt(
          stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(head->forward[lvl]));
      [&](void) {
        if (headNext.has_value()) {
          std::shared_ptr<SkipNode<T1, T2>> _x = *headNext;
          if (Nat::leb(lvl, nodeLevel)) {
            std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
                ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                    node->forward[lvl]));
            return stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                head->forward[lvl], opt_to_ptr(nodeNext));
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
  static void
  unlinkNodeAtAllLevels(const std::shared_ptr<SkipNode<T1, T2>> head,
                        const std::shared_ptr<SkipNode<T1, T2>> node,
                        const unsigned int lvl) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> headNext = ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(head->forward[lvl]));
    [&](void) {
      if (headNext.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> _x = *headNext;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
            ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(
                node->forward[lvl]));
        return stm::writeTVar<std::shared_ptr<SkipNode<T1, T2>>>(
            head->forward[lvl], opt_to_ptr(nodeNext));
      } else {
        return;
      }
    }();
    if (lvl <= 0) {
      return;
    } else {
      unsigned int lvl_ = lvl - 1;
      return SkipList<int, int>::template unlinkNodeAtAllLevels<T1, T2>(
          head, node, lvl_);
    }
  }

  template <typename T1, typename T2>
  static unsigned int
  removeAll_aux(const unsigned int fuel,
                const std::shared_ptr<SkipNode<T1, T2>> head,
                const unsigned int maxLvl, const unsigned int acc) {
    if (fuel <= 0) {
      return acc;
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt = ptr_to_opt(
          stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(head->forward[0]));
      if (firstOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
        SkipList<int, int>::template unlinkNodeAtAllLevels<T1, T2>(head, node,
                                                                   maxLvl);
        return SkipList<int, int>::template removeAll_aux<T1, T2>(
            fuel_, head, maxLvl, (acc + 1));
      } else {
        return acc;
      }
    }
  }

  template <typename T1, typename T2>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  next(const std::shared_ptr<SkipNode<T1, T2>> pair) {
    return ptr_to_opt(
        stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(pair->forward[0]));
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findPrev_aux(F0 &&eqK, const unsigned int fuel,
               const std::shared_ptr<SkipNode<T1, T2>> curr,
               const std::shared_ptr<SkipNode<T1, T2>> _x, const T1 target) {
    if (fuel <= 0) {
      return std::nullopt;
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt = ptr_to_opt(
          stm::readTVar<std::shared_ptr<SkipNode<T1, T2>>>(curr->forward[0]));
      if (nextOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        if (eqK(next0->key, target)) {
          return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(curr);
        } else {
          return SkipList<int, int>::template findPrev_aux<T1, T2>(
              eqK, fuel_, next0, curr, target);
        }
      } else {
        return std::nullopt;
      }
    }
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
      std::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
      return std::make_pair(
          SkipList<int, int>::e_SUCCESS,
          std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(node));
    } else {
      return std::make_pair(SkipList<int, int>::e_NOT_FOUND, std::nullopt);
    }
  }

  template <typename T1, typename T2>
  static std::shared_ptr<SkipList<T1, T2>> create(const T1 dummyKey,
                                                  const T2 dummyVal) {
    std::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal, (((16u - (0 + 1)) > 16u ? 0 : (16u - (0 + 1)))));
    std::shared_ptr<stm::TVar<unsigned int>> lvlTV =
        stm::newTVar<unsigned int>(0);
    std::shared_ptr<stm::TVar<unsigned int>> lenTV =
        stm::newTVar<unsigned int>(0);
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
  static bool nat_lt(const unsigned int, const unsigned int);

  static bool nat_eq(const unsigned int, const unsigned int);

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
