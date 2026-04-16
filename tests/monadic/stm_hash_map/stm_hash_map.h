#ifndef INCLUDED_STM_HASH_MAP
#define INCLUDED_STM_HASH_MAP

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stm_adapter.h>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename K, typename V> struct CHT {
  std::function<bool(K, K)> cht_eqb;
  std::function<int64_t(K)> cht_hash;
  std::vector<stm::TVar<std::shared_ptr<List<std::pair<K, V>>>>> cht_buckets;
  int64_t cht_nbuckets;
  stm::TVar<std::shared_ptr<List<std::pair<K, V>>>> cht_fallback;

  stm::TVar<std::shared_ptr<List<std::pair<K, V>>>> bucket_of(const K k) const {
    int64_t i = (this->CHT::cht_nbuckets == 0
                     ? 0
                     : this->CHT::cht_hash(k) % this->CHT::cht_nbuckets);
    return this->CHT::cht_buckets.at(i);
  }

  std::optional<V> stm_get(const K k) const {
    stm::TVar<std::shared_ptr<List<std::pair<K, V>>>> b = this->bucket_of(k);
    std::shared_ptr<List<std::pair<K, V>>> xs = stm::readTVar(b);
    return CHT<int, int>::template assoc_lookup<K, V>(this->CHT::cht_eqb, k,
                                                      xs);
  }

  std::monostate stm_put(const K k, const V v) const {
    stm::TVar<std::shared_ptr<List<std::pair<K, V>>>> b = this->bucket_of(k);
    std::shared_ptr<List<std::pair<K, V>>> xs = stm::readTVar(b);
    std::shared_ptr<List<std::pair<K, V>>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(
            this->CHT::cht_eqb, k, v, std::move(xs));
    stm::writeTVar(b, xs_);
    return std::monostate{};
  }

  std::optional<V> stm_delete(const K k) const {
    stm::TVar<std::shared_ptr<List<std::pair<K, V>>>> b = this->bucket_of(k);
    std::shared_ptr<List<std::pair<K, V>>> xs = stm::readTVar(b);
    std::pair<std::optional<V>, std::shared_ptr<List<std::pair<K, V>>>> p =
        CHT<int, int>::template assoc_remove<K, V>(this->CHT::cht_eqb, k,
                                                   std::move(xs));
    auto _cs = p.first;
    if (_cs.has_value()) {
      const V &_x = *_cs;
      stm::writeTVar(b, p.second);
      return p.first;
    } else {
      return p.first;
    }
  }

  template <MapsTo<V, std::optional<V>> F1>
  V stm_update(const K k, F1 &&f) const {
    stm::TVar<std::shared_ptr<List<std::pair<K, V>>>> b = this->bucket_of(k);
    std::shared_ptr<List<std::pair<K, V>>> xs = stm::readTVar(b);
    std::optional<V> ov =
        CHT<int, int>::template assoc_lookup<K, V>(this->CHT::cht_eqb, k, xs);
    V v = f(ov);
    std::shared_ptr<List<std::pair<K, V>>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(
            this->CHT::cht_eqb, k, v, std::move(xs));
    stm::writeTVar(b, xs_);
    return v;
  }

  V stm_get_or(const K k, const V dflt) const {
    std::optional<V> v = this->stm_get(k);
    if (v.has_value()) {
      const V &x = *v;
      return x;
    } else {
      return dflt;
    }
  }

  std::monostate put(const K k, const V v) const {
    return stm::atomically([&] {
      return [&]() {
        this->stm_put(k, v);
        return std::monostate{};
      }();
    });
  }

  std::optional<V> get(const K k) const {
    return stm::atomically([&] { return this->stm_get(k); });
  }

  std::optional<V> hash_delete(const K k) const {
    return stm::atomically([&] { return this->stm_delete(k); });
  }

  template <MapsTo<V, std::optional<V>> F1>
  V hash_update(const K k, F1 &&f) const {
    return stm::atomically([&] { return this->stm_update(k, f); });
  }

  V get_or(const K k, const V dflt) const {
    return stm::atomically([&] { return this->stm_get_or(k, dflt); });
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static std::optional<T2>
  assoc_lookup(F0 &&eqb, const T1 k,
               const std::shared_ptr<List<std::pair<T1, T2>>> &xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
            xs->v())) {
      return std::optional<T2>();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs->v());
      const T1 &k_ = d_a0.first;
      const T2 &v = d_a0.second;
      if (eqb(k, k_)) {
        return std::make_optional<T2>(v);
      } else {
        return CHT<int, int>::template assoc_lookup<T1, T2>(eqb, k, d_a1);
      }
    }
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List<std::pair<T1, T2>>>
  assoc_insert_or_replace(F0 &&eqb, const T1 k, const T2 v,
                          const std::shared_ptr<List<std::pair<T1, T2>>> &xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
            xs->v())) {
      return List<std::pair<T1, T2>>::cons(std::make_pair(k, v),
                                           List<std::pair<T1, T2>>::nil());
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs->v());
      const T1 &k_ = d_a0.first;
      const T2 &v_ = d_a0.second;
      if (eqb(k, k_)) {
        return List<std::pair<T1, T2>>::cons(std::make_pair(k, v), d_a1);
      } else {
        return List<std::pair<T1, T2>>::cons(
            std::make_pair(k_, v_),
            CHT<int, int>::template assoc_insert_or_replace<T1, T2>(eqb, k, v,
                                                                    d_a1));
      }
    }
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static std::pair<
      std::optional<T2>, std::shared_ptr<List<std::pair<T1, T2>>>>
  assoc_remove(F0 &&eqb, const T1 k,
               std::shared_ptr<List<std::pair<T1, T2>>> xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
            xs->v())) {
      return std::make_pair(std::optional<T2>(), std::move(xs));
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs->v());
      const T1 &k_ = d_a0.first;
      const T2 &v_ = d_a0.second;
      if (eqb(k, k_)) {
        return std::make_pair(std::make_optional<T2>(v_), d_a1);
      } else {
        std::pair<std::optional<T2>, std::shared_ptr<List<std::pair<T1, T2>>>>
            q = CHT<int, int>::template assoc_remove<T1, T2>(eqb, k, d_a1);
        return std::make_pair(q.first, List<std::pair<T1, T2>>::cons(
                                           std::make_pair(k_, v_), q.second));
      }
    }
  }

  template <typename T1, typename T2>
  static std::vector<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>>
  mk_buckets(const int64_t num) {
    std::vector<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>> buckets =
        {};
    std::function<std::vector<
        stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>>(unsigned int)>
        f;
    f = [&](unsigned int n)
        -> std::vector<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>> {
      if (n <= 0) {
        return buckets;
      } else {
        unsigned int n_ = n - 1;
        stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>> b = stm::atomically(
            [&] { return stm::newTVar(List<std::pair<T1, T2>>::nil()); });
        buckets.push_back(b);
        return f(n_);
      }
    };
    return f(static_cast<unsigned int>(num));
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<int64_t, T1> F1>
  static std::shared_ptr<CHT<T1, T2>> new_hash(F0 &&eqb, F1 &&hash,
                                               const int64_t requested) {
    int64_t n = std::max<int64_t>(requested, 1);
    std::vector<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>> bs =
        CHT<int, int>::template mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>> fb = stm::atomically(
          [&] { return stm::newTVar(List<std::pair<T1, T2>>::nil()); });
      std::vector<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>> v = {};
      v.push_back(fb);
      return std::make_shared<CHT<T1, T2>>(CHT<T1, T2>{eqb, hash, v, 1, fb});
    } else {
      stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>> b = bs.at(0);
      return std::make_shared<CHT<T1, T2>>(CHT<T1, T2>{eqb, hash, bs, n, b});
    }
  }
};

#endif // INCLUDED_STM_HASH_MAP
