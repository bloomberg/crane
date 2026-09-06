#ifndef INCLUDED_STM_HASH_MAP
#define INCLUDED_STM_HASH_MAP

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct CHT {
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
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
        return assoc_lookup<T1, T2>(eqb, k, *a1);
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
      const auto &[k_, v_] = a0;
      if (eqb(k, k_)) {
        return List<std::pair<T1, T2>>::cons(std::make_pair(k, v), *a1);
      } else {
        return List<std::pair<T1, T2>>::cons(
            std::make_pair(k_, v_),
            assoc_insert_or_replace<T1, T2>(eqb, k, v, *a1));
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
      auto [k_, v_] = std::move(a0);
      if (eqb(k, k_)) {
        return std::make_pair(std::make_optional<T2>(v_), *a1);
      } else {
        std::pair<std::optional<T2>, List<std::pair<T1, T2>>> q =
            assoc_remove<T1, T2>(eqb, k, *a1);
        return std::make_pair(q.first, List<std::pair<T1, T2>>::cons(
                                           std::make_pair(k_, v_), q.second));
      }
    }
  }

  template <typename K, typename V> struct CHT0 {
    std::function<bool(K, K)> cht_eqb;
    std::function<int64_t(K)> cht_hash;
    std::vector<stm::TVar<List<std::pair<K, V>>>> cht_buckets;
    int64_t cht_nbuckets;
    stm::TVar<List<std::pair<K, V>>> cht_fallback;
  };

  template <typename T1, typename T2>
  static stm::TVar<List<std::pair<T1, T2>>> bucket_of(const CHT0<T1, T2> &t,
                                                      const T1 &k) {
    int64_t i =
        (t.cht_nbuckets == 0 ? t.cht_hash(k) : t.cht_hash(k) % t.cht_nbuckets);
    return t.cht_buckets.at(i);
  }

  template <typename T1, typename T2>
  static std::optional<T2> stm_get(const CHT0<T1, T2> &t, const T1 &k) {
    stm::TVar<List<std::pair<T1, T2>>> b = bucket_of<T1, T2>(t, k);
    List<std::pair<T1, T2>> xs = stm::readTVar(b);
    return assoc_lookup<T1, T2>(t.cht_eqb, k, xs);
  }

  template <typename T1, typename T2>
  static void stm_put(const CHT0<T1, T2> &t, const T1 &k, const T2 &v) {
    stm::TVar<List<std::pair<T1, T2>>> b = bucket_of<T1, T2>(t, k);
    List<std::pair<T1, T2>> xs = stm::readTVar(b);
    List<std::pair<T1, T2>> xs_ =
        assoc_insert_or_replace<T1, T2>(t.cht_eqb, k, v, std::move(xs));
    stm::writeTVar(b, xs_);
    return;
  }

  template <typename T1, typename T2>
  static std::optional<T2> stm_delete(const CHT0<T1, T2> &t, const T1 &k) {
    stm::TVar<List<std::pair<T1, T2>>> b = bucket_of<T1, T2>(t, k);
    List<std::pair<T1, T2>> xs = stm::readTVar(b);
    std::pair<std::optional<T2>, List<std::pair<T1, T2>>> p =
        assoc_remove<T1, T2>(t.cht_eqb, k, std::move(xs));
    auto _cs = p.first;
    if (_cs.has_value()) {
      const T2 &_x = *_cs;
      stm::writeTVar(std::move(b), p.second);
      return p.first;
    } else {
      return p.first;
    }
  }

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, F2 &, std::optional<T2> &>
  static T2 stm_update(const CHT0<T1, T2> &t, const T1 &k, F2 &&f) {
    stm::TVar<List<std::pair<T1, T2>>> b = bucket_of<T1, T2>(t, k);
    List<std::pair<T1, T2>> xs = stm::readTVar(b);
    std::optional<T2> ov = assoc_lookup<T1, T2>(t.cht_eqb, k, xs);
    T2 v = f(std::move(ov));
    List<std::pair<T1, T2>> xs_ =
        assoc_insert_or_replace<T1, T2>(t.cht_eqb, k, v, std::move(xs));
    stm::writeTVar(b, xs_);
    return v;
  }

  template <typename T1, typename T2>
  static T2 stm_get_or(const CHT0<T1, T2> &t, const T1 &k, const T2 &dflt) {
    std::optional<T2> v = stm_get<T1, T2>(t, k);
    if (v.has_value()) {
      const T2 &x = *v;
      return x;
    } else {
      return dflt;
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
  static CHT0<T1, T2> new_hash(F0 &&eqb, F1 &&hash, int64_t requested) {
    int64_t n = std::max<int64_t>(requested, 1);
    std::vector<stm::TVar<List<std::pair<T1, T2>>>> bs = mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      stm::TVar<List<std::pair<T1, T2>>> fb = stm::atomically(
          [&] { return stm::newTVar(List<std::pair<T1, T2>>::nil()); });
      std::vector<stm::TVar<List<std::pair<T1, T2>>>> v = {};
      v.push_back(fb);
      return CHT0<T1, T2>{eqb, hash, v, 1, fb};
    } else {
      stm::TVar<List<std::pair<T1, T2>>> b = bs.at(0);
      return CHT0<T1, T2>{eqb, hash, bs, n, b};
    }
  }

  template <typename T1, typename T2>
  static void put(const CHT0<T1, T2> &t, const T1 &k, const T2 &v) {
    {
      stm::atomically([&] {
        return [&]() {
          stm_put<T1, T2>(t, k, v);
          return std::monostate{};
        }();
      });
      return;
    }
  }

  template <typename T1, typename T2>
  static std::optional<T2> get(const CHT0<T1, T2> &t, const T1 &k) {
    return stm::atomically([&] { return stm_get<T1, T2>(t, k); });
  }

  template <typename T1, typename T2>
  static std::optional<T2> hash_delete(const CHT0<T1, T2> &t, const T1 &k) {
    return stm::atomically([&] { return stm_delete<T1, T2>(t, k); });
  }

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, F2 &, std::optional<T2> &>
  static T2 hash_update(const CHT0<T1, T2> &t, const T1 &k, F2 &&f) {
    return stm::atomically([&] { return stm_update<T1, T2>(t, k, f); });
  }

  template <typename T1, typename T2>
  static T2 get_or(const CHT0<T1, T2> &t, const T1 &k, const T2 &dflt) {
    return stm::atomically([&] { return stm_get_or<T1, T2>(t, k, dflt); });
  }
};

#endif // INCLUDED_STM_HASH_MAP
