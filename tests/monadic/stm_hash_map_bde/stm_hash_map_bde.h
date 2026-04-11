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

template <class F, class R, class... Args>
concept MapsTo = requires(F &f, Args &...a) {
  {
    bsl::invoke(static_cast<F &>(f), static_cast<Args &>(a)...)
  } -> convertible_to<R>;
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};
  struct Cons {
    t_A d_a0;
    bsl::shared_ptr<List<t_A>> d_a1;
  };
  using variant_t = bsl::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(bsl::move(_v)) {}
  explicit List(Cons _v) : d_v_(bsl::move(_v)) {}
  static bsl::shared_ptr<List<t_A>> nil() {
    return bsl::make_shared<List<t_A>>(Nil{});
  }
  static bsl::shared_ptr<List<t_A>> cons(t_A a0,
                                         const bsl::shared_ptr<List<t_A>> &a1) {
    return bsl::make_shared<List<t_A>>(Cons{bsl::move(a0), a1});
  }
  static bsl::shared_ptr<List<t_A>> cons(t_A a0,
                                         bsl::shared_ptr<List<t_A>> &&a1) {
    return bsl::make_shared<List<t_A>>(Cons{bsl::move(a0), bsl::move(a1)});
  }
  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};
template <typename K, typename V> struct CHT {
  bsl::function<bool(K, K)> cht_eqb;
  bsl::function<int64_t(K)> cht_hash;
  bsl::vector<stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>> cht_buckets;
  int64_t cht_nbuckets;
  stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>> cht_fallback;
  stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>> bucket_of(const K k) const {
    int64_t i = this->CHT::cht_hash(k) % this->CHT::cht_nbuckets;
    return this->CHT::cht_buckets.at(i);
  }
  bsl::optional<V> stm_get(const K k) const {
    stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>> b = this->bucket_of(k);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs = stm::readTVar(b);
    return CHT<int, int>::template assoc_lookup<K, V>(this->CHT::cht_eqb, k,
                                                      xs);
  }
  std::monostate stm_put(const K k, const V v) const {
    stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>> b = this->bucket_of(k);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs = stm::readTVar(b);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(
            this->CHT::cht_eqb, k, v, bsl::move(xs));
    stm::writeTVar(b, xs_);
    return std::monostate{};
  }
  bsl::optional<V> stm_delete(const K k) const {
    stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>> b = this->bucket_of(k);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs = stm::readTVar(b);
    bsl::pair<bsl::optional<V>, bsl::shared_ptr<List<bsl::pair<K, V>>>> p =
        CHT<int, int>::template assoc_remove<K, V>(this->CHT::cht_eqb, k,
                                                   bsl::move(xs));
    if (p.first.has_value()) {
      V _x = *p.first;
      stm::writeTVar(b, p.second);
      return p.first;
    } else {
      return p.first;
    }
  }
  template <MapsTo<V, bsl::optional<V>> F1>
  V stm_update(const K k, F1 &&f) const {
    stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>> b = this->bucket_of(k);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs = stm::readTVar(b);
    bsl::optional<V> ov =
        CHT<int, int>::template assoc_lookup<K, V>(this->CHT::cht_eqb, k, xs);
    V v = f(ov);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(
            this->CHT::cht_eqb, k, v, bsl::move(xs));
    stm::writeTVar(b, xs_);
    return v;
  }
  V stm_get_or(const K k, const V dflt) const {
    bsl::optional<V> v = this->stm_get(k);
    if (v.has_value()) {
      V x = *v;
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
  bsl::optional<V> get(const K k) const {
    return stm::atomically([&] { return this->stm_get(k); });
  }
  bsl::optional<V> hash_delete(const K k) const {
    return stm::atomically([&] { return this->stm_delete(k); });
  }
  template <MapsTo<V, bsl::optional<V>> F1>
  V hash_update(const K k, F1 &&f) const {
    return stm::atomically([&] { return this->stm_update(k, f); });
  }
  V get_or(const K k, const V dflt) const {
    return stm::atomically([&] { return this->stm_get_or(k, dflt); });
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bsl::optional<T2>
  assoc_lookup(F0 &&eqb, const T1 k,
               const bsl::shared_ptr<List<bsl::pair<T1, T2>>> &xs) {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<bsl::pair<T1, T2>>::Nil)
                -> bsl::optional<T2> { return bsl::optional<T2>(); },
            [&](const typename List<bsl::pair<T1, T2>>::Cons _args)
                -> bsl::optional<T2> {
              T1 k_ = _args.d_a0.first;
              T2 v = _args.d_a0.second;
              if (eqb(k, k_)) {
                return bsl::make_optional<T2>(v);
              } else {
                return CHT<int, int>::template assoc_lookup<T1, T2>(eqb, k,
                                                                    _args.d_a1);
              }
            }},
        xs->v());
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<List<bsl::pair<T1, T2>>>
  assoc_insert_or_replace(F0 &&eqb, const T1 k, const T2 v,
                          const bsl::shared_ptr<List<bsl::pair<T1, T2>>> &xs) {
    return bsl::visit(
        bdlf::Overloaded{
            [&](const typename List<bsl::pair<T1, T2>>::Nil)
                -> bsl::shared_ptr<List<bsl::pair<T1, T2>>> {
              return List<bsl::pair<T1, T2>>::cons(
                  bsl::make_pair(k, v), List<bsl::pair<T1, T2>>::nil());
            },
            [&](const typename List<bsl::pair<T1, T2>>::Cons _args)
                -> bsl::shared_ptr<List<bsl::pair<T1, T2>>> {
              T1 k_ = _args.d_a0.first;
              T2 v_ = _args.d_a0.second;
              if (eqb(k, k_)) {
                return List<bsl::pair<T1, T2>>::cons(bsl::make_pair(k, v),
                                                     _args.d_a1);
              } else {
                return List<bsl::pair<T1, T2>>::cons(
                    bsl::make_pair(k_, v_),
                    CHT<int, int>::template assoc_insert_or_replace<T1, T2>(
                        eqb, k, v, _args.d_a1));
              }
            }},
        xs->v());
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bsl::pair<
      bsl::optional<T2>, bsl::shared_ptr<List<bsl::pair<T1, T2>>>>
  assoc_remove(F0 &&eqb, const T1 k,
               bsl::shared_ptr<List<bsl::pair<T1, T2>>> xs) {
    return bsl::visit(
        bdlf::Overloaded{
            [&](const typename List<bsl::pair<T1, T2>>::Nil)
                -> bsl::pair<bsl::optional<T2>,
                             bsl::shared_ptr<List<bsl::pair<T1, T2>>>> {
              return bsl::make_pair(bsl::optional<T2>(), xs);
            },
            [&](const typename List<bsl::pair<T1, T2>>::Cons _args)
                -> bsl::pair<bsl::optional<T2>,
                             bsl::shared_ptr<List<bsl::pair<T1, T2>>>> {
              T1 k_ = _args.d_a0.first;
              T2 v_ = _args.d_a0.second;
              if (eqb(k, k_)) {
                return bsl::make_pair(bsl::make_optional<T2>(v_), _args.d_a1);
              } else {
                bsl::pair<bsl::optional<T2>,
                          bsl::shared_ptr<List<bsl::pair<T1, T2>>>>
                    q = CHT<int, int>::template assoc_remove<T1, T2>(
                        eqb, k, _args.d_a1);
                return bsl::make_pair(q.first,
                                      List<bsl::pair<T1, T2>>::cons(
                                          bsl::make_pair(k_, v_), q.second));
              }
            }},
        xs->v());
  }
  template <typename T1, typename T2>
  static bsl::vector<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>>
  mk_buckets(const int64_t num) {
    bsl::vector<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>> buckets =
        {};
    bsl::function<bsl::vector<
        stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>>(unsigned int)>
        f;
    f = [&](unsigned int n)
        -> bsl::vector<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>> {
      if (n <= 0) {
        return buckets;
      } else {
        unsigned int n_ = n - 1;
        stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>> b = stm::atomically(
            [&] { return stm::newTVar(List<bsl::pair<T1, T2>>::nil()); });
        buckets.push_back(b);
        return f(n_);
      }
    };
    return f(static_cast<unsigned int>(num));
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<int64_t, T1> F1>
  static bsl::shared_ptr<CHT<T1, T2>> new_hash(F0 &&eqb, F1 &&hash,
                                               const int64_t requested) {
    int64_t n = bsl::max<int64_t>(requested, 1);
    bsl::vector<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>> bs =
        CHT<int, int>::template mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>> fb = stm::atomically(
          [&] { return stm::newTVar(List<bsl::pair<T1, T2>>::nil()); });
      bsl::vector<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>> v = {};
      v.push_back(fb);
      return bsl::make_shared<CHT<T1, T2>>(CHT<T1, T2>{eqb, hash, v, 1, fb});
    } else {
      stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>> b = bs.at(0);
      return bsl::make_shared<CHT<T1, T2>>(CHT<T1, T2>{eqb, hash, bs, n, b});
    }
  }
};

#endif // INCLUDED_STM_HASH_MAP_BDE
