#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
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
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct STM {};

struct TVar {};

template <typename K, typename V> struct CHT {
  std::function<bool(K, K)> cht_eqb;
  std::function<int(K)> cht_hash;
  std::vector<
      std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<K, V>>>>>>
      cht_buckets;
  int cht_nbuckets;
  std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<K, V>>>>>
      cht_fallback;
  V get_or(const K k, const V dflt) const {
    return stm::atomically([&] { return this->stm_get_or(k, dflt); });
  }
  template <MapsTo<V, std::optional<V>> F1>
  V hash_update(const K k, F1 &&f) const {
    return stm::atomically([&] { return this->stm_update(k, f); });
  }
  std::optional<V> hash_delete(const K k) const {
    return stm::atomically([&] { return this->stm_delete(k); });
  }
  std::optional<V> get(const K k) const {
    return stm::atomically([&] { return this->stm_get(k); });
  }
  void put(const K k, const V v) const {
    return stm::atomically([&] { return this->stm_put(k, v); });
  }
  V stm_get_or(const K k, const V dflt) const {
    std::optional<V> v = this->stm_get(k);
    if (v.has_value()) {
      V x = *v;
      return x;
    } else {
      return dflt;
    }
  }
  template <MapsTo<V, std::optional<V>> F1>
  V stm_update(const K k, F1 &&f) const {
    std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<K, V>>>>> b =
        this->bucket_of(k);
    std::shared_ptr<List::list<std::pair<K, V>>> xs =
        stm::readTVar<std::shared_ptr<List::list<std::pair<K, V>>>>(b);
    std::optional<V> ov = CHT::assoc_lookup<K, V>(this->CHT::cht_eqb, k, xs);
    V v = f(ov);
    std::shared_ptr<List::list<std::pair<K, V>>> xs_ =
        CHT::assoc_insert_or_replace<K, V>(this->CHT::cht_eqb, k, v, xs);
    stm::writeTVar<std::shared_ptr<List::list<std::pair<K, V>>>>(b, xs_);
    return v;
  }
  std::optional<V> stm_delete(const K k) const {
    std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<K, V>>>>> b =
        this->bucket_of(k);
    std::shared_ptr<List::list<std::pair<K, V>>> xs =
        stm::readTVar<std::shared_ptr<List::list<std::pair<K, V>>>>(b);
    std::pair<std::optional<V>, std::shared_ptr<List::list<std::pair<K, V>>>>
        p = CHT::assoc_remove<K, V>(this->CHT::cht_eqb, k, xs);
    if (p.first.has_value()) {
      V _x = *p.first;
      stm::writeTVar<std::shared_ptr<List::list<std::pair<K, V>>>>(b, p.second);
      return p.first;
    } else {
      return p.first;
    }
  }
  void stm_put(const K k, const V v) const {
    std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<K, V>>>>> b =
        this->bucket_of(k);
    std::shared_ptr<List::list<std::pair<K, V>>> xs =
        stm::readTVar<std::shared_ptr<List::list<std::pair<K, V>>>>(b);
    std::shared_ptr<List::list<std::pair<K, V>>> xs_ =
        CHT::assoc_insert_or_replace<K, V>(this->CHT::cht_eqb, k, v, xs);
    stm::writeTVar<std::shared_ptr<List::list<std::pair<K, V>>>>(b, xs_);
    return;
  }
  std::optional<V> stm_get(const K k) const {
    std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<K, V>>>>> b =
        this->bucket_of(k);
    std::shared_ptr<List::list<std::pair<K, V>>> xs =
        stm::readTVar<std::shared_ptr<List::list<std::pair<K, V>>>>(b);
    return CHT::assoc_lookup<K, V>(this->CHT::cht_eqb, k, xs);
  }
  std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<K, V>>>>>
  bucket_of(const K k) const {
    int i = this->CHT::cht_hash(k) % this->CHT::cht_nbuckets;
    return this->CHT::cht_buckets.at(i);
  }
  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::optional<T2>
  assoc_lookup(F0 &&eqb, const T1 k,
               const std::shared_ptr<List::list<std::pair<T1, T2>>> &xs) {
    return std::visit(
        Overloaded{[&](const typename List::list<std::pair<T1, T2>>::nil _args)
                       -> std::optional<T2> { return std::nullopt; },
                   [&](const typename List::list<std::pair<T1, T2>>::cons _args)
                       -> std::optional<T2> {
                     std::pair<T1, T2> p = _args._a0;
                     std::shared_ptr<List::list<std::pair<T1, T2>>> tl =
                         _args._a1;
                     T1 k_ = p.first;
                     T2 v = p.second;
                     if (eqb(k, k_)) {
                       return std::make_optional<T2>(v);
                     } else {
                       return assoc_lookup<T1, T2>(eqb, k, tl);
                     }
                   }},
        xs->v());
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<std::pair<T1, T2>>> assoc_insert_or_replace(
      F0 &&eqb, const T1 k, const T2 v,
      const std::shared_ptr<List::list<std::pair<T1, T2>>> &xs) {
    return std::visit(
        Overloaded{[&](const typename List::list<std::pair<T1, T2>>::nil _args)
                       -> std::shared_ptr<List::list<std::pair<T1, T2>>> {
                     return List::list<std::pair<T1, T2>>::ctor::cons_(
                         std::make_pair(k, v),
                         List::list<std::pair<T1, T2>>::ctor::nil_());
                   },
                   [&](const typename List::list<std::pair<T1, T2>>::cons _args)
                       -> std::shared_ptr<List::list<std::pair<T1, T2>>> {
                     std::pair<T1, T2> p = _args._a0;
                     std::shared_ptr<List::list<std::pair<T1, T2>>> tl =
                         _args._a1;
                     T1 k_ = p.first;
                     T2 v_ = p.second;
                     if (eqb(k, k_)) {
                       return List::list<std::pair<T1, T2>>::ctor::cons_(
                           std::make_pair(k, v), tl);
                     } else {
                       return List::list<std::pair<T1, T2>>::ctor::cons_(
                           std::make_pair(k_, v_),
                           assoc_insert_or_replace<T1, T2>(eqb, k, v, tl));
                     }
                   }},
        xs->v());
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::pair<std::optional<T2>,
                   std::shared_ptr<List::list<std::pair<T1, T2>>>>
  assoc_remove(F0 &&eqb, const T1 k,
               const std::shared_ptr<List::list<std::pair<T1, T2>>> &xs) {
    return std::visit(
        Overloaded{
            [&](const typename List::list<std::pair<T1, T2>>::nil _args)
                -> std::pair<std::optional<T2>,
                             std::shared_ptr<List::list<std::pair<T1, T2>>>> {
              return std::make_pair(std::nullopt, xs);
            },
            [&](const typename List::list<std::pair<T1, T2>>::cons _args)
                -> std::pair<std::optional<T2>,
                             std::shared_ptr<List::list<std::pair<T1, T2>>>> {
              std::pair<T1, T2> p = _args._a0;
              std::shared_ptr<List::list<std::pair<T1, T2>>> tl = _args._a1;
              T1 k_ = p.first;
              T2 v_ = p.second;
              if (eqb(k, k_)) {
                return std::make_pair(std::make_optional<T2>(v_), tl);
              } else {
                std::pair<std::optional<T2>,
                          std::shared_ptr<List::list<std::pair<T1, T2>>>>
                    q = assoc_remove<T1, T2>(eqb, k, tl);
                return std::make_pair(
                    q.first, List::list<std::pair<T1, T2>>::ctor::cons_(
                                 std::make_pair(k_, v_), q.second));
              }
            }},
        xs->v());
  }

  template <typename T1, typename T2>
  static std::vector<std::shared_ptr<
      stm::TVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>>>
  mk_buckets(const int num) {
    std::vector<std::shared_ptr<
        stm::TVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>>>
        buckets = {};
    std::function<std::vector<std::shared_ptr<stm::TVar<
        std::shared_ptr<List::list<std::pair<T1, T2>>>>>>(unsigned int)>
        f;
    f = [&](unsigned int n)
        -> std::vector<std::shared_ptr<
            stm::TVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>>> {
      if (n <= 0) {
        return buckets;
      } else {
        unsigned int n_ = n - 1;
        std::shared_ptr<
            stm::TVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>>
            b = stm::atomically([&] {
              return stm::newTVar<
                  std::shared_ptr<List::list<std::pair<T1, T2>>>>(
                  List::list<std::pair<T1, T2>>::ctor::nil_());
            });
        buckets.push_back(b);
        return f(n_);
      }
    };
    return f(static_cast<unsigned int>(num));
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<int, T1> F1>
  static std::shared_ptr<CHT<T1, T2>> new_hash(F0 &&eqb, F1 &&hash,
                                               const int requested) {
    int n = std::max(requested, 1);
    std::vector<std::shared_ptr<
        stm::TVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>>>
        bs = mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>>
          fb = stm::atomically([&] {
            return stm::newTVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>(
                List::list<std::pair<T1, T2>>::ctor::nil_());
          });
      std::vector<std::shared_ptr<
          stm::TVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>>>
          v = {};
      v.push_back(fb);
      return std::make_shared<CHT<T1, T2>>(CHT<T1, T2>{eqb, hash, v, 1, fb});
    } else {
      std::shared_ptr<stm::TVar<std::shared_ptr<List::list<std::pair<T1, T2>>>>>
          b = bs.at(0);
      return std::make_shared<CHT<T1, T2>>(CHT<T1, T2>{eqb, hash, bs, n, b});
    }
  }
};
