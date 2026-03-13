#ifndef INCLUDED_STM_HASH_MAP
#define INCLUDED_STM_HASH_MAP

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
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
  std::function<bool(K, K)> cht_eqb;
  std::function<int64_t(K)> cht_hash;
  std::vector<
      std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<K, V>>>>>>
      cht_buckets;
  int64_t cht_nbuckets;
  std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<K, V>>>>>
      cht_fallback;

  __attribute__((pure))
  std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<K, V>>>>>
  bucket_of(const K k) const {
    int64_t i = (this->CHT::cht_nbuckets == 0
                     ? 0
                     : this->CHT::cht_hash(k) % this->CHT::cht_nbuckets);
    return this->CHT::cht_buckets.at(i);
  }

  __attribute__((pure)) std::optional<V> stm_get(const K k) const {
    std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<K, V>>>>> b =
        this->bucket_of(k);
    std::shared_ptr<List<std::pair<K, V>>> xs = b->read();
    return CHT<int, int>::template assoc_lookup<K, V>(this->CHT::cht_eqb, k,
                                                      xs);
  }

  __attribute__((pure)) void stm_put(const K k, const V v) const {
    std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<K, V>>>>> b =
        this->bucket_of(k);
    std::shared_ptr<List<std::pair<K, V>>> xs = b->read();
    std::shared_ptr<List<std::pair<K, V>>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(
            this->CHT::cht_eqb, k, v, xs);
    b->write(xs_);
    return;
  }

  __attribute__((pure)) std::optional<V> stm_delete(const K k) const {
    std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<K, V>>>>> b =
        this->bucket_of(k);
    std::shared_ptr<List<std::pair<K, V>>> xs = b->read();
    std::pair<std::optional<V>, std::shared_ptr<List<std::pair<K, V>>>> p =
        CHT<int, int>::template assoc_remove<K, V>(this->CHT::cht_eqb, k, xs);
    if (p.first.has_value()) {
      V _x = *p.first;
      b->write(p.second);
      return p.first;
    } else {
      return p.first;
    }
  }

  template <MapsTo<V, std::optional<V>> F1>
  __attribute__((pure)) V stm_update(const K k, F1 &&f) const {
    std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<K, V>>>>> b =
        this->bucket_of(k);
    std::shared_ptr<List<std::pair<K, V>>> xs = b->read();
    std::optional<V> ov =
        CHT<int, int>::template assoc_lookup<K, V>(this->CHT::cht_eqb, k, xs);
    V v = f(std::move(ov));
    std::shared_ptr<List<std::pair<K, V>>> xs_ =
        CHT<int, int>::template assoc_insert_or_replace<K, V>(
            this->CHT::cht_eqb, k, v, xs);
    b->write(xs_);
    return v;
  }

  __attribute__((pure)) V stm_get_or(const K k, const V dflt) const {
    std::optional<V> v = this->stm_get(k);
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

  __attribute__((pure)) std::optional<V> get(const K k) const {
    return stm::atomically([&] { return this->stm_get(k); });
  }

  __attribute__((pure)) std::optional<V> hash_delete(const K k) const {
    return stm::atomically([&] { return this->stm_delete(k); });
  }

  template <MapsTo<V, std::optional<V>> F1>
  __attribute__((pure)) V hash_update(const K k, F1 &&f) const {
    return stm::atomically([&] { return this->stm_update(k, f); });
  }

  __attribute__((pure)) V get_or(const K k, const V dflt) const {
    return stm::atomically([&] { return this->stm_get_or(k, dflt); });
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static std::optional<T2>
  assoc_lookup(F0 &&eqb, const T1 k,
               const std::shared_ptr<List<std::pair<T1, T2>>> &xs) {
    return std::visit(
        Overloaded{[](const typename List<std::pair<T1, T2>>::Nil _args)
                       -> std::optional<T2> { return std::nullopt; },
                   [&](const typename List<std::pair<T1, T2>>::Cons _args)
                       -> std::optional<T2> {
                     std::pair<T1, T2> p = _args.d_a0;
                     std::shared_ptr<List<std::pair<T1, T2>>> tl = _args.d_a1;
                     T1 k_ = p.first;
                     T2 v = p.second;
                     if (eqb(k, std::move(k_))) {
                       return std::make_optional<T2>(std::move(v));
                     } else {
                       return CHT<int, int>::template assoc_lookup<T1, T2>(
                           eqb, k, tl);
                     }
                   }},
        xs->v());
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List<std::pair<T1, T2>>>
  assoc_insert_or_replace(F0 &&eqb, const T1 k, const T2 v,
                          const std::shared_ptr<List<std::pair<T1, T2>>> &xs) {
    return std::visit(
        Overloaded{
            [&](const typename List<std::pair<T1, T2>>::Nil _args)
                -> std::shared_ptr<List<std::pair<T1, T2>>> {
              return List<std::pair<T1, T2>>::ctor::Cons_(
                  std::make_pair(k, v), List<std::pair<T1, T2>>::ctor::Nil_());
            },
            [&](const typename List<std::pair<T1, T2>>::Cons _args)
                -> std::shared_ptr<List<std::pair<T1, T2>>> {
              std::pair<T1, T2> p = _args.d_a0;
              std::shared_ptr<List<std::pair<T1, T2>>> tl = _args.d_a1;
              T1 k_ = p.first;
              T2 v_ = p.second;
              if (eqb(k, std::move(k_))) {
                return List<std::pair<T1, T2>>::ctor::Cons_(
                    std::make_pair(k, v), tl);
              } else {
                return List<std::pair<T1, T2>>::ctor::Cons_(
                    std::make_pair(std::move(k_), std::move(v_)),
                    CHT<int, int>::template assoc_insert_or_replace<T1, T2>(
                        eqb, k, v, tl));
              }
            }},
        xs->v());
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static std::pair<
      std::optional<T2>, std::shared_ptr<List<std::pair<T1, T2>>>>
  assoc_remove(F0 &&eqb, const T1 k,
               std::shared_ptr<List<std::pair<T1, T2>>> xs) {
    return std::visit(
        Overloaded{[&](const typename List<std::pair<T1, T2>>::Nil _args)
                       -> std::pair<std::optional<T2>,
                                    std::shared_ptr<List<std::pair<T1, T2>>>> {
                     return std::make_pair(std::nullopt, std::move(xs));
                   },
                   [&](const typename List<std::pair<T1, T2>>::Cons _args)
                       -> std::pair<std::optional<T2>,
                                    std::shared_ptr<List<std::pair<T1, T2>>>> {
                     std::pair<T1, T2> p = _args.d_a0;
                     std::shared_ptr<List<std::pair<T1, T2>>> tl = _args.d_a1;
                     T1 k_ = p.first;
                     T2 v_ = p.second;
                     if (eqb(k, std::move(k_))) {
                       return std::make_pair(
                           std::make_optional<T2>(std::move(v_)),
                           std::move(tl));
                     } else {
                       std::pair<std::optional<T2>,
                                 std::shared_ptr<List<std::pair<T1, T2>>>>
                           q = CHT<int, int>::template assoc_remove<T1, T2>(
                               eqb, k, std::move(tl));
                       return std::make_pair(
                           std::move(q).first,
                           List<std::pair<T1, T2>>::ctor::Cons_(
                               std::make_pair(std::move(k_), std::move(v_)),
                               std::move(q).second));
                     }
                   }},
        xs->v());
  }

  template <typename T1, typename T2>
  __attribute__((pure)) static std::vector<
      std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>>>
  mk_buckets(const int64_t num) {
    std::vector<
        std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>>>
        buckets = {};
    std::function<std::vector<std::shared_ptr<
        stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>>>(unsigned int)>
        f;
    f = [&](unsigned int n)
        -> std::vector<std::shared_ptr<
            stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>>> {
      if (n <= 0) {
        return buckets;
      } else {
        unsigned int n_ = n - 1;
        std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>> b =
            stm::atomically([&] {
              return stm::newTVar<std::shared_ptr<List<std::pair<T1, T2>>>>(
                  List<std::pair<T1, T2>>::ctor::Nil_());
            });
        buckets.push_back(b);
        return f(n_);
      }
    };
    return f(static_cast<unsigned int>(num));
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<int64_t, T1> F1>
  __attribute__((pure)) static std::shared_ptr<CHT<T1, T2>>
  new_hash(F0 &&eqb, F1 &&hash, const int64_t requested) {
    int64_t n = std::max(requested, int64_t(1));
    std::vector<
        std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>>>
        bs = CHT<int, int>::template mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>> fb =
          stm::atomically([&] {
            return stm::newTVar<std::shared_ptr<List<std::pair<T1, T2>>>>(
                List<std::pair<T1, T2>>::ctor::Nil_());
          });
      std::vector<
          std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>>>
          v = {};
      v.push_back(fb);
      return std::make_shared<CHT<T1, T2>>(
          CHT<T1, T2>{eqb, hash, v, int64_t(1), fb});
    } else {
      std::shared_ptr<stm::TVar<std::shared_ptr<List<std::pair<T1, T2>>>>> b =
          bs.at(int64_t(0));
      return std::make_shared<CHT<T1, T2>>(CHT<T1, T2>{eqb, hash, bs, n, b});
    }
  }
};

#endif // INCLUDED_STM_HASH_MAP
