#ifndef INCLUDED_STM_HASH_MAP
#define INCLUDED_STM_HASH_MAP

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <stm_adapter.h>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename K, typename V> struct CHT {
  crane::fn<bool(K, K)> cht_eqb;
  crane::fn<int64_t(K)> cht_hash;
  std::vector<stm::TVar<List<std::pair<K, V>>>> cht_buckets;
  int64_t cht_nbuckets;
  stm::TVar<List<std::pair<K, V>>> cht_fallback;

  stm::TVar<List<std::pair<K, V>>> bucket_of(const K &k) const {
    auto &&_once1 = this->cht_hash(k);
    auto &&_once2 = this->cht_nbuckets;
    int64_t i = (_once2 == 0 ? _once1 : _once1 % (_once2 | (_once2 == 0)));
    return this->cht_buckets.at(i);
  }

  std::optional<V> stm_get(const K &k) const {
    stm::TVar<List<std::pair<K, V>>> b = this->bucket_of(k);
    List<std::pair<K, V>> xs = stm::readTVar(std::move(b));
    return CHT<int, int>::template assoc_lookup<K, V>(this->cht_eqb, k,
                                                      std::move(xs));
  }

  std::monostate stm_put(const K &k, const V &v) const {
    stm::TVar<List<std::pair<K, V>>> b = this->bucket_of(k);
    List<std::pair<K, V>> xs = stm::readTVar(b);
    List<std::pair<K, V>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(this->cht_eqb, k,
                                                              v, std::move(xs));
    stm::writeTVar(std::move(b), std::move(xs_));
    return std::monostate{};
  }

  std::optional<V> stm_delete(const K &k) const {
    stm::TVar<List<std::pair<K, V>>> b = this->bucket_of(k);
    List<std::pair<K, V>> xs = stm::readTVar(b);
    std::pair<std::optional<V>, List<std::pair<K, V>>> p =
        CHT<int, int>::template assoc_remove<K, V>(this->cht_eqb, k,
                                                   std::move(xs));
    auto _cs = p.first;
    if (_cs.has_value()) {
      const V &_x = *_cs;
      stm::writeTVar(std::move(b), p.second);
      return std::move(p).first;
    } else {
      return std::move(p).first;
    }
  }

  template <typename F1>
    requires std::is_invocable_r_v<V, F1 &, std::optional<V> &&>
  V stm_update(const K &k, F1 &&f) const {
    stm::TVar<List<std::pair<K, V>>> b = this->bucket_of(k);
    List<std::pair<K, V>> xs = stm::readTVar(b);
    std::optional<V> ov =
        CHT<int, int>::template assoc_lookup<K, V>(this->cht_eqb, k, xs);
    V v = f(std::move(ov));
    List<std::pair<K, V>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(this->cht_eqb, k,
                                                              v, std::move(xs));
    stm::writeTVar(std::move(b), std::move(xs_));
    return v;
  }

  V stm_get_or(const K &k, const V &dflt) const {
    std::optional<V> v = this->stm_get(k);
    if (v.has_value()) {
      const V &x = *v;
      return x;
    } else {
      return dflt;
    }
  }

  std::monostate put(const K &k, const V &v) const {
    return stm::atomically([&] {
      return [&]() {
        this->stm_put(k, v);
        return std::monostate{};
      }();
    });
  }

  std::optional<V> get(const K &k) const {
    return stm::atomically([&] { return this->stm_get(k); });
  }

  std::optional<V> hash_delete(const K &k) const {
    return stm::atomically([&] { return this->stm_delete(k); });
  }

  template <typename F1> V hash_update(const K &k, F1 &&f) const {
    return stm::atomically([&] { return this->stm_update(k, f); });
  }

  V get_or(const K &k, const V &dflt) const {
    return stm::atomically([&] { return this->stm_get_or(k, dflt); });
  }

  template <typename T1, typename T2, typename F0>
  static std::optional<T2> assoc_lookup(F0 &&eqb, const T1 &k,
                                        const List<std::pair<T1, T2>> &xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(xs.v())) {
      return std::optional<T2>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs.v());
      const auto &[k_, v] = a0;
      if (eqb(k, k_)) {
        return std::make_optional<T2>(v);
      } else {
        return CHT<int, int>::template assoc_lookup<T1, T2>(eqb, k, *a1);
      }
    }
  }

  template <typename T1, typename T2, typename F0>
  static List<std::pair<T1, T2>>
  assoc_insert_or_replace(F0 &&eqb, const T1 &k, const T2 &v,
                          const List<std::pair<T1, T2>> &xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(xs.v())) {
      return List<std::pair<T1, T2>>::cons(std::make_pair(k, v),
                                           List<std::pair<T1, T2>>::nil());
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs.v());
      const auto &[k_, v_] = a0;
      if (eqb(k, k_)) {
        return List<std::pair<T1, T2>>::cons(std::make_pair(k, v), *a1);
      } else {
        return List<std::pair<T1, T2>>::cons(
            std::make_pair(k_, v_),
            CHT<int, int>::template assoc_insert_or_replace<T1, T2>(eqb, k, v,
                                                                    *a1));
      }
    }
  }

  template <typename T1, typename T2, typename F0>
  static std::pair<std::optional<T2>, List<std::pair<T1, T2>>>
  assoc_remove(F0 &&eqb, const T1 &k, const List<std::pair<T1, T2>> &xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(xs.v())) {
      return std::make_pair(std::optional<T2>(), xs);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs.v());
      const auto &[k_, v_] = a0;
      if (eqb(k, k_)) {
        return std::make_pair(std::make_optional<T2>(v_), *a1);
      } else {
        std::pair<std::optional<T2>, List<std::pair<T1, T2>>> q =
            CHT<int, int>::template assoc_remove<T1, T2>(eqb, k, *a1);
        return std::make_pair(std::move(q).first,
                              List<std::pair<T1, T2>>::cons(
                                  std::make_pair(k_, v_), std::move(q).second));
      }
    }
  }

  template <typename T1, typename T2>
  static std::vector<stm::TVar<List<std::pair<T1, T2>>>>
  mk_buckets(int64_t num) {
    std::vector<stm::TVar<List<std::pair<T1, T2>>>> buckets = {};
    {
      uint64_t _lc1_n = static_cast<unsigned int>(num);
      uint64_t _lc1_loop_n = std::move(_lc1_n);
      while (true) {
        if (_lc1_loop_n <= 0) {
          return buckets;
        } else {
          uint64_t n_ = _lc1_loop_n - 1;
          stm::TVar<List<std::pair<T1, T2>>> b = stm::atomically(
              [&] { return stm::newTVar(List<std::pair<T1, T2>>::nil()); });
          buckets.push_back(std::move(b));
          _lc1_loop_n = n_;
        }
      }
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
  static CHT<T1, T2> new_hash(F0 &&eqb, F1 &&hash, int64_t requested) {
    int64_t n = std::max<int64_t>(requested, 1);
    std::vector<stm::TVar<List<std::pair<T1, T2>>>> bs =
        CHT<int, int>::template mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      stm::TVar<List<std::pair<T1, T2>>> fb = stm::atomically(
          [&] { return stm::newTVar(List<std::pair<T1, T2>>::nil()); });
      std::vector<stm::TVar<List<std::pair<T1, T2>>>> v = {};
      v.push_back(fb);
      return CHT<T1, T2>{eqb, hash, std::move(v), 1, std::move(fb)};
    } else {
      stm::TVar<List<std::pair<T1, T2>>> b = bs.at(0);
      return CHT<T1, T2>{eqb, hash, std::move(bs), n, std::move(b)};
    }
  }
};

#endif // INCLUDED_STM_HASH_MAP
