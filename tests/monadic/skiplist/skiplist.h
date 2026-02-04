#include <algorithm>
#include <any>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <skipnode.h>
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

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    unsigned int length0() const {
      return std::visit(
          Overloaded{
              [](const typename List::list<A>::nil _args) -> unsigned int {
                return 0;
              },
              [](const typename List::list<A>::cons _args) -> unsigned int {
                std::shared_ptr<List::list<A>> l_ = _args._a1;
                return (l_->length0() + 1);
              }},
          this->v());
    }
    std::shared_ptr<List::list<A>>
    app(const std::shared_ptr<List::list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a, l1->app(m));
                     }},
          this->v());
    }
  };
};

struct Nat {
  static bool eqb(const unsigned int n, const unsigned int m);

  static bool leb(const unsigned int n, const unsigned int m);

  static bool ltb(const unsigned int n, const unsigned int m);
};

template <typename T1>
std::shared_ptr<List::list<T1>> repeat(const T1 x, const unsigned int n) {
  if (n <= 0) {
    return List::list<T1>::ctor::nil_();
  } else {
    unsigned int k = n - 1;
    return List::list<T1>::ctor::cons_(x, repeat<T1>(x, k));
  }
}

template <typename T1>
std::shared_ptr<List::list<T1>>
firstn(const unsigned int n, const std::shared_ptr<List::list<T1>> &l) {
  if (n <= 0) {
    return List::list<T1>::ctor::nil_();
  } else {
    unsigned int n0 = n - 1;
    return std::visit(
        Overloaded{[](const typename List::list<T1>::nil _args)
                       -> std::shared_ptr<List::list<T1>> {
                     return List::list<T1>::ctor::nil_();
                   },
                   [&](const typename List::list<T1>::cons _args)
                       -> std::shared_ptr<List::list<T1>> {
                     T1 a = _args._a0;
                     std::shared_ptr<List::list<T1>> l0 = _args._a1;
                     return List::list<T1>::ctor::cons_(a, firstn<T1>(n0, l0));
                   }},
        l->v());
  }
}

template <typename T1>
std::shared_ptr<List::list<T1>> rev(const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(Overloaded{[](const typename List::list<T1>::nil _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 return List::list<T1>::ctor::nil_();
                               },
                               [](const typename List::list<T1>::cons _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 T1 x = _args._a0;
                                 std::shared_ptr<List::list<T1>> l_ = _args._a1;
                                 return rev<T1>(l_)->app(
                                     List::list<T1>::ctor::cons_(
                                         x, List::list<T1>::ctor::nil_()));
                               }},
                    l->v());
}

struct STM {};

struct TVar {};

template <typename K, typename V> struct SkipList {
  std::shared_ptr<SkipNode<K, V>> slHead;
  unsigned int slMaxLevel;
  std::shared_ptr<stm::TVar<unsigned int>> slLevel;
  std::shared_ptr<stm::TVar<unsigned int>> slLength;
  template <MapsTo<bool, K, K> F0>
  std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>>
  findPath(F0 &&ltK, const K target) const {
    unsigned int lvl = stm::readTVar<unsigned int>(this->SkipList::slLevel);
    return SkipList<int, int>::template findPath_aux<K, V>(
        ltK, this->SkipList::slHead, target, lvl,
        List::list<std::shared_ptr<SkipNode<K, V>>>::ctor::nil_());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::optional<V> lookup(F0 &&ltK, F1 &&eqK, const K k) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> std::optional<V> { return std::nullopt; },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> std::optional<V> {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
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
            }},
        path->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  void insert(F0 &&ltK, F1 &&eqK, const K k, const V v,
              const unsigned int newLevel) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> fullPath =
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (newLevel + 1));
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> void {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
                if (eqK(existing->key, k)) {
                  return stm::writeTVar<V>(existing->value, v);
                } else {
                  std::shared_ptr<SkipNode<K, V>> newN =
                      SkipNode<K, V>::create(k, v, newLevel);
                  SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                  unsigned int curLvl =
                      stm::readTVar<unsigned int>(this->SkipList::slLevel);
                  [&](void) {
                    if (Nat::ltb(curLvl, newLevel)) {
                      return stm::writeTVar<unsigned int>(
                          this->SkipList::slLevel, newLevel);
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
                std::shared_ptr<SkipNode<K, V>> newN =
                    SkipNode<K, V>::create(k, v, newLevel);
                SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                unsigned int curLvl =
                    stm::readTVar<unsigned int>(this->SkipList::slLevel);
                [&](void) {
                  if (Nat::ltb(curLvl, newLevel)) {
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
            }},
        fullPath->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  void remove(F0 &&ltK, F1 &&eqK, const K k) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> void {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
                if (eqK(node->key, k)) {
                  std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>>
                      fullPath = SkipList<int, int>::template extendPath<K, V>(
                          path, this->SkipList::slHead, (node->level + 1));
                  SkipList<int, int>::template unlinkNode<K, V>(fullPath, node);
                  unsigned int len =
                      stm::readTVar<unsigned int>(this->SkipList::slLength);
                  return stm::writeTVar<unsigned int>(
                      this->SkipList::slLength,
                      (((len - (0 + 1)) > len ? 0 : (len - (0 + 1)))));
                } else {
                  return;
                }
              } else {
                return;
              }
            }},
        path->v());
  }
  std::optional<std::pair<K, V>> minimum() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
            this->SkipList::slHead->forward[0]);
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      V v = stm::readTVar<V>(node->value);
      return std::make_optional<std::pair<K, V>>(std::make_pair(node->key, v));
    } else {
      return std::nullopt;
    }
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool member(F0 &&ltK, F1 &&eqK, const K k) const {
    std::optional<V> result = this->lookup(ltK, eqK, k);
    return [&](void) {
      if (result.has_value()) {
        V _x = *result;
        return true;
      } else {
        return false;
      }
    }();
  }
  bool isEmpty() const {
    unsigned int len = stm::readTVar<unsigned int>(this->SkipList::slLength);
    return Nat::eqb(len, 0);
  }
  unsigned int length() const {
    return stm::readTVar<unsigned int>(this->SkipList::slLength);
  }
  bool exists_() const { return this->member(); }
  std::optional<std::shared_ptr<SkipNode<K, V>>> front() const {
    return stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
        this->SkipList::slHead->forward[0]);
  }
  std::optional<std::shared_ptr<SkipNode<K, V>>> back() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
            this->SkipList::slHead->forward[0]);
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> first = *firstOpt;
      return SkipList<int, int>::template findLast_aux<K, V>(10000u, first);
    } else {
      return std::nullopt;
    }
  }
  std::optional<std::pair<K, V>> popFront() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
            this->SkipList::slHead->forward[0]);
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level,
          (((16u - (0 + 1)) > 16u ? 0 : (16u - (0 + 1)))));
      unsigned int len = stm::readTVar<unsigned int>(this->SkipList::slLength);
      stm::writeTVar<unsigned int>(
          this->SkipList::slLength,
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
        (((16u - (0 + 1)) > 16u ? 0 : (16u - (0 + 1)))));
    stm::writeTVar<unsigned int>(this->SkipList::slLength, 0);
    stm::writeTVar<unsigned int>(this->SkipList::slLevel, 0);
    return count;
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  void add(F0 &&ltK, F1 &&eqK, const K k, const V v,
           const unsigned int newLevel) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> fullPath =
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (newLevel + 1));
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> void {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
                if (eqK(existing->key, k)) {
                  return stm::writeTVar<V>(existing->value, v);
                } else {
                  std::shared_ptr<SkipNode<K, V>> newN =
                      SkipNode<K, V>::create(k, v, newLevel);
                  SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                  unsigned int curLvl =
                      stm::readTVar<unsigned int>(this->SkipList::slLevel);
                  [&](void) {
                    if (Nat::ltb(curLvl, newLevel)) {
                      return stm::writeTVar<unsigned int>(
                          this->SkipList::slLevel, newLevel);
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
                std::shared_ptr<SkipNode<K, V>> newN =
                    SkipNode<K, V>::create(k, v, newLevel);
                SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                unsigned int curLvl =
                    stm::readTVar<unsigned int>(this->SkipList::slLevel);
                [&](void) {
                  if (Nat::ltb(curLvl, newLevel)) {
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
            }},
        fullPath->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool addUnique(F0 &&ltK, F1 &&eqK, const K k, const V v,
                 const unsigned int newLevel) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> fullPath =
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (newLevel + 1));
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> bool { return false; },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> bool {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
                if (eqK(existing->key, k)) {
                  return false;
                } else {
                  std::shared_ptr<SkipNode<K, V>> newN =
                      SkipNode<K, V>::create(k, v, newLevel);
                  SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                  unsigned int curLvl =
                      stm::readTVar<unsigned int>(this->SkipList::slLevel);
                  [&](void) {
                    if (Nat::ltb(curLvl, newLevel)) {
                      return stm::writeTVar<unsigned int>(
                          this->SkipList::slLevel, newLevel);
                    } else {
                      return;
                    }
                  }();
                  unsigned int len =
                      stm::readTVar<unsigned int>(this->SkipList::slLength);
                  stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                               (len + 1));
                  return true;
                }
              } else {
                std::shared_ptr<SkipNode<K, V>> newN =
                    SkipNode<K, V>::create(k, v, newLevel);
                SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                unsigned int curLvl =
                    stm::readTVar<unsigned int>(this->SkipList::slLevel);
                [&](void) {
                  if (Nat::ltb(curLvl, newLevel)) {
                    return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                                        newLevel);
                  } else {
                    return;
                  }
                }();
                unsigned int len =
                    stm::readTVar<unsigned int>(this->SkipList::slLength);
                stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                             (len + 1));
                return true;
              }
            }},
        fullPath->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::optional<std::shared_ptr<SkipNode<K, V>>> find(F0 &&ltK, F1 &&eqK,
                                                      const K k) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> std::optional<std::shared_ptr<SkipNode<K, V>>> {
              return std::nullopt;
            },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> std::optional<std::shared_ptr<SkipNode<K, V>>> {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
                if (eqK(node->key, k)) {
                  return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(
                      node);
                } else {
                  return std::nullopt;
                }
              } else {
                return std::nullopt;
              }
            }},
        path->v());
  }
  template <MapsTo<bool, K, K> F0>
  std::optional<std::shared_ptr<SkipNode<K, V>>>
  previous(F0 &&eqK, const std::shared_ptr<SkipNode<K, V>> pair) const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> firstOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
            this->SkipList::slHead->forward[0]);
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
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> std::optional<std::shared_ptr<SkipNode<K, V>>> {
              return std::nullopt;
            },
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                   _args) -> std::optional<std::shared_ptr<SkipNode<K, V>>> {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
                return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(
                    node);
              } else {
                return std::nullopt;
              }
            }},
        path->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::optional<std::shared_ptr<SkipNode<K, V>>>
  findUpperBound(F0 &&ltK, F1 &&eqK, const K k) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> std::optional<std::shared_ptr<SkipNode<K, V>>> {
              return std::nullopt;
            },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> std::optional<std::shared_ptr<SkipNode<K, V>>> {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
                if (eqK(node->key, k)) {
                  return stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      node->forward[0]);
                } else {
                  return std::make_optional<std::shared_ptr<SkipNode<K, V>>>(
                      node);
                }
              } else {
                return std::nullopt;
              }
            }},
        path->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  bool removePair(F0 &&ltK, F1 &&eqK,
                  const std::shared_ptr<SkipNode<K, V>> pair) const {
    K k = pair->key;
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args) -> bool { return false; },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> bool {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
                if (eqK(node->key, k)) {
                  std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>>
                      fullPath = SkipList<int, int>::template extendPath<K, V>(
                          path, this->SkipList::slHead, (node->level + 1));
                  SkipList<int, int>::template unlinkNode<K, V>(fullPath, node);
                  unsigned int len =
                      stm::readTVar<unsigned int>(this->SkipList::slLength);
                  stm::writeTVar<unsigned int>(
                      this->SkipList::slLength,
                      (((len - (0 + 1)) > len ? 0 : (len - (0 + 1)))));
                  return true;
                } else {
                  return false;
                }
              } else {
                return false;
              }
            }},
        path->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::pair<std::shared_ptr<SkipNode<K, V>>, bool>
  bde_add(F0 &&ltK, F1 &&eqK, const K key0, const V data0,
          const unsigned int level) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, key0);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> fullPath =
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (level + 1));
    std::optional<std::shared_ptr<SkipNode<K, V>>> curFront =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
            this->SkipList::slHead->forward[0]);
    bool isNewFront;
    if (curFront.has_value()) {
      std::shared_ptr<SkipNode<K, V>> frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    return std::visit(
        Overloaded{
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                    _args) -> std::pair<std::shared_ptr<SkipNode<K, V>>, bool> {
              std::shared_ptr<SkipNode<K, V>> newN =
                  SkipNode<K, V>::create(key0, data0, level);
              return std::make_pair(newN, true);
            },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args) -> std::pair<std::shared_ptr<SkipNode<K, V>>, bool> {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
                if (eqK(existing->key, key0)) {
                  stm::writeTVar<V>(existing->value, data0);
                  return std::make_pair(existing, false);
                } else {
                  std::shared_ptr<SkipNode<K, V>> newN =
                      SkipNode<K, V>::create(key0, data0, level);
                  SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                  unsigned int curLvl =
                      stm::readTVar<unsigned int>(this->SkipList::slLevel);
                  [&](void) {
                    if (Nat::ltb(curLvl, level)) {
                      return stm::writeTVar<unsigned int>(
                          this->SkipList::slLevel, level);
                    } else {
                      return;
                    }
                  }();
                  unsigned int len =
                      stm::readTVar<unsigned int>(this->SkipList::slLength);
                  stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                               (len + 1));
                  return std::make_pair(newN, isNewFront);
                }
              } else {
                std::shared_ptr<SkipNode<K, V>> newN =
                    SkipNode<K, V>::create(key0, data0, level);
                SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                unsigned int curLvl =
                    stm::readTVar<unsigned int>(this->SkipList::slLevel);
                [&](void) {
                  if (Nat::ltb(curLvl, level)) {
                    return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                                        level);
                  } else {
                    return;
                  }
                }();
                unsigned int len =
                    stm::readTVar<unsigned int>(this->SkipList::slLength);
                stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                             (len + 1));
                return std::make_pair(newN, isNewFront);
              }
            }},
        fullPath->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::pair<
      std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>,
      bool>
  bde_addUnique(F0 &&ltK, F1 &&eqK, const K key0, const V data0,
                const unsigned int level) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, key0);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> fullPath =
        SkipList<int, int>::template extendPath<K, V>(
            path, this->SkipList::slHead, (level + 1));
    std::optional<std::shared_ptr<SkipNode<K, V>>> curFront =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
            this->SkipList::slHead->forward[0]);
    bool isNewFront;
    if (curFront.has_value()) {
      std::shared_ptr<SkipNode<K, V>> frontNode = *curFront;
      isNewFront = ltK(key0, frontNode->key);
    } else {
      isNewFront = true;
    }
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args)
                -> std::pair<
                    std::pair<unsigned int,
                              std::optional<std::shared_ptr<SkipNode<K, V>>>>,
                    bool> {
              return std::make_pair(
                  std::make_pair(SkipList<int, int>::e_INVALID, std::nullopt),
                  false);
            },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args)
                -> std::pair<
                    std::pair<unsigned int,
                              std::optional<std::shared_ptr<SkipNode<K, V>>>>,
                    bool> {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> existing = *nextOpt;
                if (eqK(existing->key, key0)) {
                  return std::make_pair(
                      std::make_pair(SkipList<int, int>::e_DUPLICATE,
                                     std::nullopt),
                      false);
                } else {
                  std::shared_ptr<SkipNode<K, V>> newN =
                      SkipNode<K, V>::create(key0, data0, level);
                  SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                  unsigned int curLvl =
                      stm::readTVar<unsigned int>(this->SkipList::slLevel);
                  [&](void) {
                    if (Nat::ltb(curLvl, level)) {
                      return stm::writeTVar<unsigned int>(
                          this->SkipList::slLevel, level);
                    } else {
                      return;
                    }
                  }();
                  unsigned int len =
                      stm::readTVar<unsigned int>(this->SkipList::slLength);
                  stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                               (len + 1));
                  return std::make_pair(
                      std::make_pair(
                          SkipList<int, int>::e_SUCCESS,
                          std::make_optional<std::shared_ptr<SkipNode<K, V>>>(
                              newN)),
                      isNewFront);
                }
              } else {
                std::shared_ptr<SkipNode<K, V>> newN =
                    SkipNode<K, V>::create(key0, data0, level);
                SkipList<int, int>::template linkNode<K, V>(fullPath, newN);
                unsigned int curLvl =
                    stm::readTVar<unsigned int>(this->SkipList::slLevel);
                [&](void) {
                  if (Nat::ltb(curLvl, level)) {
                    return stm::writeTVar<unsigned int>(this->SkipList::slLevel,
                                                        level);
                  } else {
                    return;
                  }
                }();
                unsigned int len =
                    stm::readTVar<unsigned int>(this->SkipList::slLength);
                stm::writeTVar<unsigned int>(this->SkipList::slLength,
                                             (len + 1));
                return std::make_pair(
                    std::make_pair(
                        SkipList<int, int>::e_SUCCESS,
                        std::make_optional<std::shared_ptr<SkipNode<K, V>>>(
                            newN)),
                    isNewFront);
              }
            }},
        fullPath->v());
  }
  template <MapsTo<bool, K, K> F0, MapsTo<bool, K, K> F1>
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_find(F0 &&ltK, F1 &&eqK, const K key0) const {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<K, V>>>> path =
        this->findPath(ltK, key0);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::nil
                   _args)
                -> std::pair<unsigned int,
                             std::optional<std::shared_ptr<SkipNode<K, V>>>> {
              return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                                    std::nullopt);
            },
            [&](const typename List::list<std::shared_ptr<SkipNode<K, V>>>::cons
                    _args)
                -> std::pair<unsigned int,
                             std::optional<std::shared_ptr<SkipNode<K, V>>>> {
              std::shared_ptr<SkipNode<K, V>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<K, V>>> nextOpt =
                  stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<K, V>> node = *nextOpt;
                if (eqK(node->key, key0)) {
                  return std::make_pair(
                      SkipList<int, int>::e_SUCCESS,
                      std::make_optional<std::shared_ptr<SkipNode<K, V>>>(
                          node));
                } else {
                  return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                                        std::nullopt);
                }
              } else {
                return std::make_pair(SkipList<int, int>::e_NOT_FOUND,
                                      std::nullopt);
              }
            }},
        path->v());
  }
  std::pair<unsigned int, std::optional<std::shared_ptr<SkipNode<K, V>>>>
  bde_front() const {
    std::optional<std::shared_ptr<SkipNode<K, V>>> frontOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
            this->SkipList::slHead->forward[0]);
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
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<K, V>>>>(
            this->SkipList::slHead->forward[0]);
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<K, V>> node = *firstOpt;
      SkipList<int, int>::template unlinkFirstFromHead<K, V>(
          this->SkipList::slHead, node, node->level,
          (((16u - (0 + 1)) > 16u ? 0 : (16u - (0 + 1)))));
      unsigned int len = stm::readTVar<unsigned int>(this->SkipList::slLength);
      stm::writeTVar<unsigned int>(
          this->SkipList::slLength,
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
  bool bde_exists() const { return this->member(); }
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
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              curr->forward[level]);
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
  static std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
  findPath_aux(
      F0 &&ltK, const std::shared_ptr<SkipNode<T1, T2>> curr, const T1 target,
      const unsigned int level,
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &acc) {
    std::shared_ptr<SkipNode<T1, T2>> pred =
        SkipList<int, int>::template findPred<T1, T2>(ltK, curr, target, level);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> acc_ =
        List::list<std::shared_ptr<SkipNode<T1, T2>>>::ctor::cons_(pred, acc);
    if (level <= 0) {
      return acc_;
    } else {
      unsigned int level_ = level - 1;
      return SkipList<int, int>::template findPath_aux<T1, T2>(
          ltK, pred, target, level_, acc_);
    }
  }

  template <typename T1, typename T2>
  static void linkAtLevel(const std::shared_ptr<SkipNode<T1, T2>> pred,
                          const std::shared_ptr<SkipNode<T1, T2>> newNode,
                          const unsigned int level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> oldNext =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            pred->forward[level]);
    stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        pred->forward[level],
        std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(newNode));
    return stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        newNode->forward[level], oldNext);
  }

  template <typename T1, typename T2>
  static void linkNode_aux(
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &preds,
      const std::shared_ptr<SkipNode<T1, T2>> newNode,
      const unsigned int level) {
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args) -> void {
              std::shared_ptr<SkipNode<T1, T2>> pred = _args._a0;
              std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
                  rest = _args._a1;
              if (level <= 0) {
                return SkipList<int, int>::template linkAtLevel<T1, T2>(
                    pred, newNode, 0);
              } else {
                unsigned int level_ = level - 1;
                SkipList<int, int>::template linkAtLevel<T1, T2>(pred, newNode,
                                                                 level);
                return SkipList<int, int>::template linkNode_aux<T1, T2>(
                    rest, newNode, level_);
              }
            }},
        preds->v());
  }

  template <typename T1, typename T2>
  static std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
  extendPath(
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &path,
      const std::shared_ptr<SkipNode<T1, T2>> head, const unsigned int needed) {
    unsigned int have = path->length0();
    if (Nat::leb(needed, have)) {
      return path;
    } else {
      return path->app(repeat<std::shared_ptr<SkipNode<T1, T2>>>(
          head, (((needed - have) > needed ? 0 : (needed - have)))));
    }
  }

  template <typename T1, typename T2>
  static void
  linkNode(const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
               &path,
           const std::shared_ptr<SkipNode<T1, T2>> newNode) {
    unsigned int lvl = newNode->level;
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
        relevantPath =
            firstn<std::shared_ptr<SkipNode<T1, T2>>>((lvl + 1), path);
    return SkipList<int, int>::template linkNode_aux<T1, T2>(
        rev<std::shared_ptr<SkipNode<T1, T2>>>(relevantPath), newNode, lvl);
  }

  template <typename T1, typename T2>
  static void unlinkAtLevel(const std::shared_ptr<SkipNode<T1, T2>> pred,
                            const std::shared_ptr<SkipNode<T1, T2>> target,
                            const unsigned int level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> targetNext =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            target->forward[level]);
    return stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        pred->forward[level], targetNext);
  }

  template <typename T1, typename T2>
  static void unlinkNode_aux(
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &preds,
      const std::shared_ptr<SkipNode<T1, T2>> target,
      const unsigned int level) {
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args) -> void {
              std::shared_ptr<SkipNode<T1, T2>> pred = _args._a0;
              std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
                  rest = _args._a1;
              if (level <= 0) {
                return SkipList<int, int>::template unlinkAtLevel<T1, T2>(
                    pred, target, 0);
              } else {
                unsigned int level_ = level - 1;
                SkipList<int, int>::template unlinkAtLevel<T1, T2>(pred, target,
                                                                   level);
                return SkipList<int, int>::template unlinkNode_aux<T1, T2>(
                    rest, target, level_);
              }
            }},
        preds->v());
  }

  template <typename T1, typename T2>
  static void unlinkNode(
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &path,
      const std::shared_ptr<SkipNode<T1, T2>> target) {
    unsigned int lvl = target->level;
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
        relevantPath =
            firstn<std::shared_ptr<SkipNode<T1, T2>>>((lvl + 1), path);
    return SkipList<int, int>::template unlinkNode_aux<T1, T2>(
        rev<std::shared_ptr<SkipNode<T1, T2>>>(relevantPath), target, lvl);
  }

  template <typename T1, typename T2>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findLast_aux(const unsigned int fuel,
               const std::shared_ptr<SkipNode<T1, T2>> curr) {
    if (fuel <= 0) {
      return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(curr);
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              curr->forward[0]);
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
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              node->forward[0]);
      return stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
          head->forward[0], nodeNext);
    } else {
      unsigned int lvl_ = lvl - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> headNext =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              head->forward[lvl]);
      [&](void) {
        if (headNext.has_value()) {
          std::shared_ptr<SkipNode<T1, T2>> _x = *headNext;
          if (Nat::leb(lvl, nodeLevel)) {
            std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
                stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                    node->forward[lvl]);
            return stm::writeTVar<
                std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                head->forward[lvl], nodeNext);
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
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> headNext =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            head->forward[lvl]);
    [&](void) {
      if (headNext.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> _x = *headNext;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
            stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                node->forward[lvl]);
        return stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            head->forward[lvl], nodeNext);
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
                const unsigned int maxLvl) {
    if (fuel <= 0) {
      return 0;
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              head->forward[0]);
      if (firstOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
        SkipList<int, int>::template unlinkNodeAtAllLevels<T1, T2>(head, node,
                                                                   maxLvl);
        unsigned int rest = SkipList<int, int>::template removeAll_aux<T1, T2>(
            fuel_, head, maxLvl);
        return (rest + 1);
      } else {
        return 0;
      }
    }
  }

  template <typename T1, typename T2>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  next(const std::shared_ptr<SkipNode<T1, T2>> pair) {
    return stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        pair->forward[0]);
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
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              curr->forward[0]);
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
