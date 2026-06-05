#ifndef INCLUDED_STM_HASH_MAP
#define INCLUDED_STM_HASH_MAP

#include <any>
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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename K, typename V> struct CHT {
  std::function<bool(K, K)> cht_eqb;
  std::function<int64_t(K)> cht_hash;
  std::vector<stm::TVar<List<std::pair<K, V>>>> cht_buckets;
  int64_t cht_nbuckets;
  stm::TVar<List<std::pair<K, V>>> cht_fallback;

  stm::TVar<List<std::pair<K, V>>> bucket_of(const K &k) const {
    int64_t i =
        (this->cht_nbuckets == 0 ? 0 : this->cht_hash(k) % this->cht_nbuckets);
    return this->cht_buckets.at(i);
  }

  std::optional<V> stm_get(const K &k) const {
    stm::TVar<List<std::pair<K, V>>> b = this->bucket_of(k);
    List<std::pair<K, V>> xs = stm::readTVar(b);
    return CHT<int, int>::template assoc_lookup<K, V>(this->cht_eqb, k, xs);
  }

  std::monostate stm_put(const K &k, const V &v) const {
    stm::TVar<List<std::pair<K, V>>> b = this->bucket_of(k);
    List<std::pair<K, V>> xs = stm::readTVar(b);
    List<std::pair<K, V>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(this->cht_eqb, k,
                                                              v, std::move(xs));
    stm::writeTVar(b, xs_);
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
      return p.first;
    } else {
      return p.first;
    }
  }

  template <typename F1>
    requires std::is_invocable_r_v<V, F1 &, std::optional<V> &>
  V stm_update(const K &k, F1 &&f) const {
    stm::TVar<List<std::pair<K, V>>> b = this->bucket_of(k);
    List<std::pair<K, V>> xs = stm::readTVar(b);
    std::optional<V> ov =
        CHT<int, int>::template assoc_lookup<K, V>(this->cht_eqb, k, xs);
    V v = f(std::move(ov));
    List<std::pair<K, V>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(this->cht_eqb, k,
                                                              v, std::move(xs));
    stm::writeTVar(b, xs_);
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
    CHT<K, V> _self_val = *this;
    return stm::atomically([&] {
      return [=]() mutable {
        _self_val.stm_put(k, v);
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

  template <typename F1>
    requires std::is_invocable_r_v<V, F1 &, std::optional<V> &>
  V hash_update(const K &k, F1 &&f) const {
    return stm::atomically([&] { return this->stm_update(k, f); });
  }

  V get_or(const K &k, const V &dflt) const {
    return stm::atomically([&] { return this->stm_get_or(k, dflt); });
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static std::optional<T2> assoc_lookup(F0 &&eqb, const T1 &k,
                                        const List<std::pair<T1, T2>> &xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(xs.v())) {
      return std::optional<T2>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs.v());
      const T1 &k_ = a0.first;
      const T2 &v = a0.second;
      if (eqb(k, k_)) {
        return std::make_optional<T2>(v);
      } else {
        return CHT<int, int>::template assoc_lookup<T1, T2>(eqb, k, *a1);
      }
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<std::pair<T1, T2>>
  assoc_insert_or_replace(F0 &&eqb, T1 k, T2 v,
                          const List<std::pair<T1, T2>> &xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(xs.v())) {
      return List<std::pair<T1, T2>>::cons(std::make_pair(k, v),
                                           List<std::pair<T1, T2>>::nil());
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs.v());
      const T1 &k_ = a0.first;
      const T2 &v_ = a0.second;
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
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static std::pair<std::optional<T2>, List<std::pair<T1, T2>>>
  assoc_remove(F0 &&eqb, const T1 &k, List<std::pair<T1, T2>> xs) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(
            xs.v_mut())) {
      return std::make_pair(std::optional<T2>(), xs);
    } else {
      auto &[a0, a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(xs.v_mut());
      T1 k_ = std::move(a0.first);
      T2 v_ = std::move(a0.second);
      if (eqb(k, k_)) {
        return std::make_pair(std::make_optional<T2>(v_), *a1);
      } else {
        std::pair<std::optional<T2>, List<std::pair<T1, T2>>> q =
            CHT<int, int>::template assoc_remove<T1, T2>(eqb, k, *a1);
        return std::make_pair(q.first, List<std::pair<T1, T2>>::cons(
                                           std::make_pair(k_, v_), q.second));
      }
    }
  }

  template <typename T1, typename T2>
  static std::vector<stm::TVar<List<std::pair<T1, T2>>>>
  mk_buckets(int64_t num) {
    std::vector<stm::TVar<List<std::pair<T1, T2>>>> buckets = {};
    auto f_impl =
        [&](auto &_self_f,
            uint64_t n) -> std::vector<stm::TVar<List<std::pair<T1, T2>>>> {
      if (n <= 0) {
        return buckets;
      } else {
        uint64_t n_ = n - 1;
        stm::TVar<List<std::pair<T1, T2>>> b = stm::atomically(
            [&] { return stm::newTVar(List<std::pair<T1, T2>>::nil()); });
        buckets.push_back(b);
        return _self_f(_self_f, n_);
      }
    };
    auto f =
        [&](uint64_t n) -> std::vector<stm::TVar<List<std::pair<T1, T2>>>> {
      return f_impl(f_impl, n);
    };
    return f(static_cast<unsigned int>(num));
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<int64_t, F1 &, T1 &>
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
      return CHT<T1, T2>{eqb, hash, v, 1, fb};
    } else {
      stm::TVar<List<std::pair<T1, T2>>> b = bs.at(0);
      return CHT<T1, T2>{eqb, hash, bs, n, b};
    }
  }
};

#endif // INCLUDED_STM_HASH_MAP
