#ifndef INCLUDED_STM_HASH_MAP_BDE
#define INCLUDED_STM_HASH_MAP_BDE

#include <bdlf_overloaded.h>
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
#include <mini_stm.h>

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
  // CREATORS
  explicit List(Nil _v) : d_v_(bsl::move(_v)) {}
  explicit List(Cons _v) : d_v_(bsl::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;
    static bsl::shared_ptr<List<t_A>> Nil_() {
      return bsl::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }
    static bsl::shared_ptr<List<t_A>>
    Cons_(t_A a0, const bsl::shared_ptr<List<t_A>> &a1) {
      return bsl::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
    static bsl::unique_ptr<List<t_A>> Nil_uptr() {
      return bsl::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }
    static bsl::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const bsl::shared_ptr<List<t_A>> &a1) {
      return bsl::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };
  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};
struct STM {};
struct TVar {};
template <typename K, typename V> struct CHT {
  bsl::function<bool(K, K)> cht_eqb;
  bsl::function<int64_t(K)> cht_hash;
  bsl::vector<
      bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>>>
      cht_buckets;
  int64_t cht_nbuckets;
  bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>>
      cht_fallback;
  __attribute__((pure))
  bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>>
  bucket_of(const K k) const {
    int64_t i = this->CHT::cht_hash(k) % this->CHT::cht_nbuckets;
    return this->CHT::cht_buckets.at(i);
  }
  __attribute__((pure)) bsl::optional<V> stm_get(const K k) const {
    bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>> b =
        this->bucket_of(k);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs =
        stm::readTVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>(b);
    return CHT<int, int>::template assoc_lookup<K, V>(this->CHT::cht_eqb, k,
                                                      xs);
  }
  __attribute__((pure)) void stm_put(const K k, const V v) const {
    bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>> b =
        this->bucket_of(k);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs =
        stm::readTVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>(b);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(
            this->CHT::cht_eqb, k, v, xs);
    stm::writeTVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>(b, xs_);
    return;
  }
  __attribute__((pure)) bsl::optional<V> stm_delete(const K k) const {
    bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>> b =
        this->bucket_of(k);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs =
        stm::readTVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>(b);
    bsl::pair<bsl::optional<V>, bsl::shared_ptr<List<bsl::pair<K, V>>>> p =
        CHT<int, int>::template assoc_remove<K, V>(this->CHT::cht_eqb, k, xs);
    if (p.first.has_value()) {
      V _x = *p.first;
      stm::writeTVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>(b, p.second);
      return p.first;
    } else {
      return p.first;
    }
  }
  template <MapsTo<V, bsl::optional<V>> F1>
  __attribute__((pure)) V stm_update(const K k, F1 &&f) const {
    bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>> b =
        this->bucket_of(k);
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs =
        stm::readTVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>(b);
    bsl::optional<V> ov =
        CHT<int, int>::template assoc_lookup<K, V>(this->CHT::cht_eqb, k, xs);
    V v = f(bsl::move(ov));
    bsl::shared_ptr<List<bsl::pair<K, V>>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(
            this->CHT::cht_eqb, k, v, xs);
    stm::writeTVar<bsl::shared_ptr<List<bsl::pair<K, V>>>>(b, xs_);
    return v;
  }
  __attribute__((pure)) V stm_get_or(const K k, const V dflt) const {
    bsl::optional<V> v = this->stm_get(k);
    if (v.has_value()) {
      V x = *v;
      return x;
    } else {
      return dflt;
    }
  }
  __attribute__((pure)) void put(const K k, const V v) const {
    return stm::atomically([&] { return this->stm_put(k, v); });
  }
  __attribute__((pure)) bsl::optional<V> get(const K k) const {
    return stm::atomically([&] { return this->stm_get(k); });
  }
  __attribute__((pure)) bsl::optional<V> hash_delete(const K k) const {
    return stm::atomically([&] { return this->stm_delete(k); });
  }
  template <MapsTo<V, bsl::optional<V>> F1>
  __attribute__((pure)) V hash_update(const K k, F1 &&f) const {
    return stm::atomically([&] { return this->stm_update(k, f); });
  }
  __attribute__((pure)) V get_or(const K k, const V dflt) const {
    return stm::atomically([&] { return this->stm_get_or(k, dflt); });
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bsl::optional<T2>
  assoc_lookup(F0 &&eqb, const T1 k,
               const bsl::shared_ptr<List<bsl::pair<T1, T2>>> &xs) {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<bsl::pair<T1, T2>>::Nil _args)
                -> bsl::optional<T2> { return bsl::nullopt; },
            [&](const typename List<bsl::pair<T1, T2>>::Cons _args)
                -> bsl::optional<T2> {
              bsl::pair<T1, T2> p = _args.d_a0;
              bsl::shared_ptr<List<bsl::pair<T1, T2>>> tl = _args.d_a1;
              T1 k_ = p.first;
              T2 v = p.second;
              if (eqb(k, bsl::move(k_))) {
                return bsl::make_optional<T2>(bsl::move(v));
              } else {
                return CHT<int, int>::template assoc_lookup<T1, T2>(eqb, k, tl);
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
            [&](const typename List<bsl::pair<T1, T2>>::Nil _args)
                -> bsl::shared_ptr<List<bsl::pair<T1, T2>>> {
              return List<bsl::pair<T1, T2>>::ctor::Cons_(
                  bsl::make_pair(k, v), List<bsl::pair<T1, T2>>::ctor::Nil_());
            },
            [&](const typename List<bsl::pair<T1, T2>>::Cons _args)
                -> bsl::shared_ptr<List<bsl::pair<T1, T2>>> {
              bsl::pair<T1, T2> p = _args.d_a0;
              bsl::shared_ptr<List<bsl::pair<T1, T2>>> tl = _args.d_a1;
              T1 k_ = p.first;
              T2 v_ = p.second;
              if (eqb(k, bsl::move(k_))) {
                return List<bsl::pair<T1, T2>>::ctor::Cons_(
                    bsl::make_pair(k, v), tl);
              } else {
                return List<bsl::pair<T1, T2>>::ctor::Cons_(
                    bsl::make_pair(bsl::move(k_), bsl::move(v_)),
                    CHT<int, int>::template assoc_insert_or_replace<T1, T2>(
                        eqb, k, v, tl));
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
            [&](const typename List<bsl::pair<T1, T2>>::Nil _args)
                -> bsl::pair<bsl::optional<T2>,
                             bsl::shared_ptr<List<bsl::pair<T1, T2>>>> {
              return bsl::make_pair(bsl::nullopt, bsl::move(xs));
            },
            [&](const typename List<bsl::pair<T1, T2>>::Cons _args)
                -> bsl::pair<bsl::optional<T2>,
                             bsl::shared_ptr<List<bsl::pair<T1, T2>>>> {
              bsl::pair<T1, T2> p = _args.d_a0;
              bsl::shared_ptr<List<bsl::pair<T1, T2>>> tl = _args.d_a1;
              T1 k_ = p.first;
              T2 v_ = p.second;
              if (eqb(k, bsl::move(k_))) {
                return bsl::make_pair(bsl::make_optional<T2>(bsl::move(v_)),
                                      bsl::move(tl));
              } else {
                bsl::pair<bsl::optional<T2>,
                          bsl::shared_ptr<List<bsl::pair<T1, T2>>>>
                    q = CHT<int, int>::template assoc_remove<T1, T2>(
                        eqb, k, bsl::move(tl));
                return bsl::make_pair(
                    bsl::move(q).first,
                    List<bsl::pair<T1, T2>>::ctor::Cons_(
                        bsl::make_pair(bsl::move(k_), bsl::move(v_)),
                        bsl::move(q).second));
              }
            }},
        xs->v());
  }
  template <typename T1, typename T2>
  __attribute__((pure)) static bsl::vector<
      bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>>>
  mk_buckets(const int64_t num) {
    bsl::vector<
        bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>>>
        buckets = {};
    bsl::function<bsl::vector<bsl::shared_ptr<
        stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>>>(unsigned int)>
        f;
    f = [&](unsigned int n)
        -> bsl::vector<bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>>> {
      if (n <= 0) {
        return buckets;
      } else {
        unsigned int n_ = n - 1;
        bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>> b =
            stm::atomically([&] {
              return stm::newTVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>(
                  List<bsl::pair<T1, T2>>::ctor::Nil_());
            });
        buckets.push_back(b);
        return f(n_);
      }
    };
    return f(static_cast<unsigned int>(num));
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<int64_t, T1> F1>
  __attribute__((pure)) static bsl::shared_ptr<CHT<T1, T2>>
  new_hash(F0 &&eqb, F1 &&hash, const int64_t requested) {
    int64_t n = bsl::max(requested, int64_t(1));
    bsl::vector<
        bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>>>
        bs = CHT<int, int>::template mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>> fb =
          stm::atomically([&] {
            return stm::newTVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>(
                List<bsl::pair<T1, T2>>::ctor::Nil_());
          });
      bsl::vector<
          bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>>>
          v = {};
      v.push_back(fb);
      return bsl::make_shared<CHT<T1, T2>>(
          CHT<T1, T2>{eqb, hash, v, int64_t(1), fb});
    } else {
      bsl::shared_ptr<stm::TVar<bsl::shared_ptr<List<bsl::pair<T1, T2>>>>> b =
          bs.at(int64_t(0));
      return bsl::make_shared<CHT<T1, T2>>(CHT<T1, T2>{eqb, hash, bs, n, b});
    }
  }
};

#endif // INCLUDED_STM_HASH_MAP_BDE
