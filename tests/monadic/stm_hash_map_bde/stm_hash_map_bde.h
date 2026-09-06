#ifndef INCLUDED_STM_HASH_MAP_BDE
#define INCLUDED_STM_HASH_MAP_BDE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
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
#include <utility>
#include <variant>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <typename t_A> struct List;
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
  template <typename _U> List(const List<_U> &_other) {
    if (bsl::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->d_v_ = Nil{};
    } else {
      const auto &[d_a, d_l] = std::get<typename List<_U>::Cons>(_other.v());
      this->d_v_ = Cons{[&]() -> t_A {
                          if constexpr (std::is_same_v<_U, std::any>) {
                            return crane_any_cast<t_A>(d_a);
                          } else {
                            return t_A(d_a);
                          }
                        }(),
                        (d_l ? bsl::make_shared<List<t_A>>(*d_l) : nullptr)};
    }
  }
  static List<t_A> nil() { return List<t_A>(Nil{}); }
  static List<t_A> cons(t_A a, List<t_A> l) {
    return List<t_A>(
        Cons{bsl::move(a), bsl::make_shared<List<t_A>>(bsl::move(l))});
  }
  // MANIPULATORS
  ~List() {
    crane::small_vector<bsl::shared_ptr<List<t_A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = bsl::get_if<Cons>(&_v)) {
        if (_alt->d_l) {
          _stack.push_back(bsl::move(_alt->d_l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = bsl::move(_stack.back());
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
  inline variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};
struct CHT {
  template <typename T1, typename T2, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::optional<T2> assoc_lookup(F0 &&eqb, const T1 &k,
                                        const List<bsl::pair<T1, T2>> &xs) {
    if (bsl::holds_alternative<typename List<bsl::pair<T1, T2>>::Nil>(xs.v())) {
      return bsl::optional<T2>();
    } else {
      const auto &[d_a0, d_a1] =
          bsl::get<typename List<bsl::pair<T1, T2>>::Cons>(xs.v());
      auto [k_, v] = d_a0;
      if (eqb(k, k_)) {
        return bsl::make_optional<T2>(v);
      } else {
        return assoc_lookup<T1, T2>(eqb, k, *d_a1);
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
      auto [k_, v_] = d_a0;
      if (eqb(k, k_)) {
        return List<bsl::pair<T1, T2>>::cons(bsl::make_pair(k, v), *d_a1);
      } else {
        return List<bsl::pair<T1, T2>>::cons(
            bsl::make_pair(k_, v_),
            assoc_insert_or_replace<T1, T2>(eqb, k, v, *d_a1));
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
      auto [k_, v_] = bsl::move(d_a0);
      if (eqb(k, k_)) {
        return bsl::make_pair(bsl::make_optional<T2>(v_), *d_a1);
      } else {
        bsl::pair<bsl::optional<T2>, List<bsl::pair<T1, T2>>> q =
            assoc_remove<T1, T2>(eqb, k, *d_a1);
        return bsl::make_pair(q.first, List<bsl::pair<T1, T2>>::cons(
                                           bsl::make_pair(k_, v_), q.second));
      }
    }
  }
  template <typename t_K, typename t_V> struct CHT0 {
    bsl::function<bool(t_K, t_K)> cht_eqb;
    bsl::function<int64_t(t_K)> cht_hash;
    bsl::vector<stm::TVar<List<bsl::pair<t_K, t_V>>>> cht_buckets;
    int64_t cht_nbuckets;
    stm::TVar<List<bsl::pair<t_K, t_V>>> cht_fallback;
  };
  template <typename T1, typename T2>
  static stm::TVar<List<bsl::pair<T1, T2>>> bucket_of(const CHT0<T1, T2> &t,
                                                      const T1 &k) {
    int64_t i = (t.cht_nbuckets == 0 ? 0 : t.cht_hash(k) % t.cht_nbuckets);
    return t.cht_buckets.at(i);
  }
  template <typename T1, typename T2>
  static bsl::optional<T2> stm_get(const CHT0<T1, T2> &t, const T1 &k) {
    stm::TVar<List<bsl::pair<T1, T2>>> b = bucket_of<T1, T2>(t, k);
    List<bsl::pair<T1, T2>> xs = stm::readTVar(b);
    return assoc_lookup<T1, T2>(t.cht_eqb, k, xs);
  }
  template <typename T1, typename T2>
  static void stm_put(const CHT0<T1, T2> &t, const T1 &k, const T2 &v) {
    stm::TVar<List<bsl::pair<T1, T2>>> b = bucket_of<T1, T2>(t, k);
    List<bsl::pair<T1, T2>> xs = stm::readTVar(b);
    List<bsl::pair<T1, T2>> xs_ =
        assoc_insert_or_replace<T1, T2>(t.cht_eqb, k, v, bsl::move(xs));
    stm::writeTVar(b, xs_);
    return;
  }
  template <typename T1, typename T2>
  static bsl::optional<T2> stm_delete(const CHT0<T1, T2> &t, const T1 &k) {
    stm::TVar<List<bsl::pair<T1, T2>>> b = bucket_of<T1, T2>(t, k);
    List<bsl::pair<T1, T2>> xs = stm::readTVar(b);
    bsl::pair<bsl::optional<T2>, List<bsl::pair<T1, T2>>> p =
        assoc_remove<T1, T2>(t.cht_eqb, k, bsl::move(xs));
    auto _cs = p.first;
    if (_cs.has_value()) {
      T2 _x = *_cs;
      stm::writeTVar(bsl::move(b), p.second);
      return p.first;
    } else {
      return p.first;
    }
  }
  template <typename T1, typename T2, typename F2>
    requires bsl::is_invocable_r_v<T2, F2 &, bsl::optional<T2> &>
  static T2 stm_update(const CHT0<T1, T2> &t, const T1 &k, F2 &&f) {
    stm::TVar<List<bsl::pair<T1, T2>>> b = bucket_of<T1, T2>(t, k);
    List<bsl::pair<T1, T2>> xs = stm::readTVar(b);
    bsl::optional<T2> ov = assoc_lookup<T1, T2>(t.cht_eqb, k, xs);
    T2 v = f(bsl::move(ov));
    List<bsl::pair<T1, T2>> xs_ =
        assoc_insert_or_replace<T1, T2>(t.cht_eqb, k, v, bsl::move(xs));
    stm::writeTVar(b, xs_);
    return v;
  }
  template <typename T1, typename T2>
  static T2 stm_get_or(const CHT0<T1, T2> &t, const T1 &k, const T2 &dflt) {
    bsl::optional<T2> v = stm_get<T1, T2>(t, k);
    if (v.has_value()) {
      T2 x = *v;
      return x;
    } else {
      return dflt;
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
  static CHT0<T1, T2> new_hash(F0 &&eqb, F1 &&hash, int64_t requested) {
    int64_t n = bsl::max<int64_t>(requested, 1);
    bsl::vector<stm::TVar<List<bsl::pair<T1, T2>>>> bs = mk_buckets<T1, T2>(n);
    bool empt = bs.empty();
    if (empt) {
      stm::TVar<List<bsl::pair<T1, T2>>> fb = stm::atomically(
          [&] { return stm::newTVar(List<bsl::pair<T1, T2>>::nil()); });
      bsl::vector<stm::TVar<List<bsl::pair<T1, T2>>>> v = {};
      v.push_back(fb);
      return CHT0<T1, T2>{eqb, hash, v, 1, fb};
    } else {
      stm::TVar<List<bsl::pair<T1, T2>>> b = bs.at(0);
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
  static bsl::optional<T2> get(const CHT0<T1, T2> &t, const T1 &k) {
    return stm::atomically([&] { return stm_get<T1, T2>(t, k); });
  }
  template <typename T1, typename T2>
  static bsl::optional<T2> hash_delete(const CHT0<T1, T2> &t, const T1 &k) {
    return stm::atomically([&] { return stm_delete<T1, T2>(t, k); });
  }
  template <typename T1, typename T2, typename F2>
    requires bsl::is_invocable_r_v<T2, F2 &, bsl::optional<T2> &>
  static T2 hash_update(const CHT0<T1, T2> &t, const T1 &k, F2 &&f) {
    return stm::atomically([&] { return stm_update<T1, T2>(t, k, f); });
  }
  template <typename T1, typename T2>
  static T2 get_or(const CHT0<T1, T2> &t, const T1 &k, const T2 &dflt) {
    return stm::atomically([&] { return stm_get_or<T1, T2>(t, k, dflt); });
  }
};

#endif // INCLUDED_STM_HASH_MAP_BDE
