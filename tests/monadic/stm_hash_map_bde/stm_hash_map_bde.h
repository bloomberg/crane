#ifndef INCLUDED_STM_HASH_MAP_BDE
#define INCLUDED_STM_HASH_MAP_BDE

#include <bdlf_overloaded.h>
#include <bdls_filesystemutil.h>
#include <bsl_concepts.h>
#include <bsl_cstdint.h>
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
#include <stm_adapter.h>
#include <variant>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};
  struct Cons {
    t_A d_a;
    bsl::shared_ptr<List<t_A>> d_l;
  };
  using variant_t = bsl::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}
  explicit List(Nil _v) : d_v_(_v) {}
  explicit List(Cons _v) : d_v_(bsl::move(_v)) {}
  template <typename _U> explicit List(const List<_U> &_other) {
    if (bsl::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->d_v_ = Nil{};
    } else {
      const auto &[d_a, d_l] = std::get<typename List<_U>::Cons>(_other.v());
      this->d_v_ = Cons{
          [&]() -> t_A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (d_a.type() == typeid(t_A))
                return std::any_cast<t_A>(d_a);
              if constexpr (requires {
                              typename t_A::first_type;
                              typename t_A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(d_a);
                return t_A{
                    [&]() -> typename t_A::first_type {
                      if constexpr (std::is_same_v<typename t_A::first_type,
                                                   std::any>)
                        return _k;
                      else
                        return std::any_cast<typename t_A::first_type>(_k);
                    }(),
                    [&]() -> typename t_A::second_type {
                      if constexpr (std::is_same_v<typename t_A::second_type,
                                                   std::any>)
                        return _v;
                      else
                        return std::any_cast<typename t_A::second_type>(_v);
                    }()};
              }
              return std::any_cast<t_A>(d_a);
            } else
              return t_A(d_a);
          }(),
          d_l ? std::make_shared<List<t_A>>(*d_l) : nullptr};
    }
  }
  static List<t_A> nil() { return List(Nil{}); }
  static List<t_A> cons(t_A a, List<t_A> l) {
    return List(Cons{bsl::move(a), bsl::make_shared<List<t_A>>(bsl::move(l))});
  }
  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};
template <typename K, typename V> struct CHT {
  bsl::function<bool(K, K)> cht_eqb;
  bsl::function<int64_t(K)> cht_hash;
  bsl::vector<stm::TVar<List<bsl::pair<K, V>>>> cht_buckets;
  int64_t cht_nbuckets;
  stm::TVar<List<bsl::pair<K, V>>> cht_fallback;
  stm::TVar<List<bsl::pair<K, V>>> bucket_of(const K &k) const {
    int64_t i = this->cht_hash(k) % this->cht_nbuckets;
    return this->cht_buckets.at(i);
  }
  bsl::optional<V> stm_get(const K &k) const {
    stm::TVar<List<bsl::pair<K, V>>> b = this->bucket_of(k);
    List<bsl::pair<K, V>> xs = stm::readTVar(b);
    return CHT<int, int>::template assoc_lookup<K, V>(this->cht_eqb, k, xs);
  }
  std::monostate stm_put(const K &k, const V &v) const {
    stm::TVar<List<bsl::pair<K, V>>> b = this->bucket_of(k);
    List<bsl::pair<K, V>> xs = stm::readTVar(b);
    List<bsl::pair<K, V>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(this->cht_eqb, k,
                                                              v, bsl::move(xs));
    stm::writeTVar(b, xs_);
    return std::monostate{};
  }
  bsl::optional<V> stm_delete(const K &k) const {
    stm::TVar<List<bsl::pair<K, V>>> b = this->bucket_of(k);
    List<bsl::pair<K, V>> xs = stm::readTVar(b);
    bsl::pair<bsl::optional<V>, List<bsl::pair<K, V>>> p =
        CHT<int, int>::template assoc_remove<K, V>(this->cht_eqb, k,
                                                   bsl::move(xs));
    auto _cs = p.first;
    if (_cs.has_value()) {
      V _x = *_cs;
      stm::writeTVar(bsl::move(b), p.second);
      return p.first;
    } else {
      return p.first;
    }
  }
  template <typename F1>
    requires bsl::is_invocable_r_v<V, F1 &, bsl::optional<V> &>
  V stm_update(const K &k, F1 &&f) const {
    stm::TVar<List<bsl::pair<K, V>>> b = this->bucket_of(k);
    List<bsl::pair<K, V>> xs = stm::readTVar(b);
    bsl::optional<V> ov =
        CHT<int, int>::template assoc_lookup<K, V>(this->cht_eqb, k, xs);
    V v = f(bsl::move(ov));
    List<bsl::pair<K, V>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(this->cht_eqb, k,
                                                              v, bsl::move(xs));
    stm::writeTVar(b, xs_);
    return v;
  }
  V stm_get_or(const K &k, const V &dflt) const {
    bsl::optional<V> v = this->stm_get(k);
    if (v.has_value()) {
      V x = *v;
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
  bsl::optional<V> get(const K &k) const {
    return stm::atomically([&] { return this->stm_get(k); });
  }
  bsl::optional<V> hash_delete(const K &k) const {
    return stm::atomically([&] { return this->stm_delete(k); });
  }
  template <typename F1>
    requires bsl::is_invocable_r_v<V, F1 &, bsl::optional<V> &>
  V hash_update(const K &k, F1 &&f) const {
    return stm::atomically([&] { return this->stm_update(k, f); });
  }
  V get_or(const K &k, const V &dflt) const {
    return stm::atomically([&] { return this->stm_get_or(k, dflt); });
  }
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::optional<T2> assoc_lookup(F0 &&eqb, const T1 &k,
                                        const List<bsl::pair<T1, T2>> &xs) {
    if (bsl::holds_alternative<typename List<bsl::pair<T1, T2>>::Nil>(xs.v())) {
      return bsl::optional<T2>();
    } else {
      const auto &[d_a0, d_a1] =
          bsl::get<typename List<bsl::pair<T1, T2>>::Cons>(xs.v());
      T1 k_ = d_a0.first;
      T2 v = d_a0.second;
      if (eqb(k, k_)) {
        return bsl::make_optional<T2>(v);
      } else {
        return CHT<int, int>::template assoc_lookup<T1, T2>(eqb, k, *d_a1);
      }
    }
  }
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<bsl::pair<T1, T2>>
  assoc_insert_or_replace(F0 &&eqb, T1 k, T2 v,
                          const List<bsl::pair<T1, T2>> &xs) {
    if (bsl::holds_alternative<typename List<bsl::pair<T1, T2>>::Nil>(xs.v())) {
      return List<bsl::pair<T1, T2>>::cons(bsl::make_pair(k, v),
                                           List<bsl::pair<T1, T2>>::nil());
    } else {
      const auto &[d_a0, d_a1] =
          bsl::get<typename List<bsl::pair<T1, T2>>::Cons>(xs.v());
      T1 k_ = d_a0.first;
      T2 v_ = d_a0.second;
      if (eqb(k, k_)) {
        return List<bsl::pair<T1, T2>>::cons(bsl::make_pair(k, v), *d_a1);
      } else {
        return List<bsl::pair<T1, T2>>::cons(
            bsl::make_pair(k_, v_),
            CHT<int, int>::template assoc_insert_or_replace<T1, T2>(eqb, k, v,
                                                                    *d_a1));
      }
    }
  }
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::pair<bsl::optional<T2>, List<bsl::pair<T1, T2>>>
  assoc_remove(F0 &&eqb, const T1 &k, List<bsl::pair<T1, T2>> xs) {
    if (bsl::holds_alternative<typename List<bsl::pair<T1, T2>>::Nil>(
            xs.v_mut())) {
      return bsl::make_pair(bsl::optional<T2>(), xs);
    } else {
      auto &[d_a0, d_a1] =
          bsl::get<typename List<bsl::pair<T1, T2>>::Cons>(xs.v_mut());
      T1 k_ = std::move(d_a0.first);
      T2 v_ = std::move(d_a0.second);
      if (eqb(k, k_)) {
        return bsl::make_pair(bsl::make_optional<T2>(v_), *d_a1);
      } else {
        bsl::pair<bsl::optional<T2>, List<bsl::pair<T1, T2>>> q =
            CHT<int, int>::template assoc_remove<T1, T2>(eqb, k, *d_a1);
        return bsl::make_pair(q.first, List<bsl::pair<T1, T2>>::cons(
                                           bsl::make_pair(k_, v_), q.second));
      }
    }
  }
  template <typename T1, typename T2>
  static bsl::vector<stm::TVar<List<bsl::pair<T1, T2>>>>
  mk_buckets(int64_t num) {
    bsl::vector<stm::TVar<List<bsl::pair<T1, T2>>>> buckets = {};
    auto f_impl =
        [&](auto &_self_f,
            unsigned int n) -> bsl::vector<stm::TVar<List<bsl::pair<T1, T2>>>> {
      if (n <= 0) {
        return buckets;
      } else {
        unsigned int n_ = n - 1;
        stm::TVar<List<bsl::pair<T1, T2>>> b = stm::atomically(
            [&] { return stm::newTVar(List<bsl::pair<T1, T2>>::nil()); });
        buckets.push_back(b);
        return _self_f(_self_f, n_);
      }
    };
    auto f =
        [&](unsigned int n) -> bsl::vector<stm::TVar<List<bsl::pair<T1, T2>>>> {
      return f_impl(f_impl, n);
    };
    return f(static_cast<unsigned int>(num));
  }
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             bsl::is_invocable_r_v<int64_t, F1 &, T1 &>
  static CHT<T1, T2> new_hash(F0 &&eqb, F1 &&hash, int64_t requested) {
    int64_t n = bsl::max<int64_t>(requested, 1);
    bsl::vector<stm::TVar<List<bsl::pair<T1, T2>>>> bs =
        CHT<int, int>::template mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      stm::TVar<List<bsl::pair<T1, T2>>> fb = stm::atomically(
          [&] { return stm::newTVar(List<bsl::pair<T1, T2>>::nil()); });
      bsl::vector<stm::TVar<List<bsl::pair<T1, T2>>>> v = {};
      v.push_back(fb);
      return CHT<T1, T2>{eqb, hash, v, 1, fb};
    } else {
      stm::TVar<List<bsl::pair<T1, T2>>> b = bs.at(0);
      return CHT<T1, T2>{eqb, hash, bs, n, b};
    }
  }
};

#endif // INCLUDED_STM_HASH_MAP_BDE
