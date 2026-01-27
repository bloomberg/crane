#include <bdlf_overloaded.h>
#include <bsl_algorithm.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>
#include <bsl_vector.h>
#include <fstream>
#include <mini_stm.h>

using namespace BloombergLP;

template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <class F, class R, class... Args>
concept MapsTo = requires(F& f, Args&... a) {
    {
        bsl::invoke(static_cast<F&>(f), static_cast<Args&>(a)...)
    } -> convertible_to<R>;
};

struct List {
    template <typename A>
    struct list {
      public:
        struct nil {
        };
        struct cons {
            A                               _a0;
            bsl::shared_ptr<List::list<A> > _a1;
        };
        using variant_t = bsl::variant<nil, cons>;
      private:
        variant_t v_;
        explicit list(nil x)
        : v_(bsl::move(x))
        {
        }
        explicit list(cons x)
        : v_(bsl::move(x))
        {
        }
      public:
        struct ctor {
            ctor() = delete;
            static bsl::shared_ptr<List::list<A> > nil_()
            {
                return bsl::shared_ptr<List::list<A> >(
                                                     new List::list<A>(nil{}));
            }
            static bsl::shared_ptr<List::list<A> > cons_(
                                     A                                      a0,
                                     const bsl::shared_ptr<List::list<A> >& a1)
            {
                return bsl::shared_ptr<List::list<A> >(
                                              new List::list<A>(cons{a0, a1}));
            }
        };
        const variant_t& v() const { return v_; }
    };
};

struct STM {
};

struct TVar {
};

template <typename K, typename V>
struct CHT {
    bsl::function<bool(K, K)> cht_eqb;
    bsl::function<int(K)>     cht_hash;
    bsl::vector<bsl::shared_ptr<
        stm::TVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > > > >
                              cht_buckets;
    int                       cht_nbuckets;
    bsl::shared_ptr<
        stm::TVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > > >
        cht_fallback;
    bsl::shared_ptr<
        stm::TVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > > >
    bucket_of(const K k) const
    {
        int i = this->CHT::cht_hash(k) % this->CHT::cht_nbuckets;
        return this->CHT::cht_buckets.at(i);
    }
    bsl::optional<V> stm_get(const K k) const
    {
        bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > > >
                                                       b = this->bucket_of(k);
        bsl::shared_ptr<List::list<bsl::pair<K, V> > > xs =
             stm::readTVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > >(b);
        return CHT::assoc_lookup<K, V>(this->CHT::cht_eqb, k, xs);
    }
    void stm_put(const K k, const V v) const
    {
        bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > > >
                                                       b = this->bucket_of(k);
        bsl::shared_ptr<List::list<bsl::pair<K, V> > > xs =
             stm::readTVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > >(b);
        bsl::shared_ptr<List::list<bsl::pair<K, V> > > xs_ =
              CHT::assoc_insert_or_replace<K, V>(this->CHT::cht_eqb, k, v, xs);
        stm::writeTVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > >(b,
                                                                        xs_);
        return;
    }
    bsl::optional<V> stm_delete(const K k) const
    {
        bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > > >
                                                       b = this->bucket_of(k);
        bsl::shared_ptr<List::list<bsl::pair<K, V> > > xs =
             stm::readTVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > >(b);
        bsl::pair<bsl::optional<V>,
                  bsl::shared_ptr<List::list<bsl::pair<K, V> > > >
            p = CHT::assoc_remove<K, V>(this->CHT::cht_eqb, k, xs);
        if (p.first.has_value()) {
            V _x = *p.first;
            stm::writeTVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > >(
                                                                     b,
                                                                     p.second);
            return p.first;
        }
        else {
            return p.first;
        }
    }
    template <MapsTo<V, bsl::optional<V> > F1>
    V stm_update(const K k, F1&& f) const
    {
        bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > > >
                                                       b = this->bucket_of(k);
        bsl::shared_ptr<List::list<bsl::pair<K, V> > > xs =
             stm::readTVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > >(b);
        bsl::optional<V> ov = CHT::assoc_lookup<K, V>(this->CHT::cht_eqb,
                                                      k,
                                                      xs);
        V                v  = f(ov);
        bsl::shared_ptr<List::list<bsl::pair<K, V> > > xs_ =
              CHT::assoc_insert_or_replace<K, V>(this->CHT::cht_eqb, k, v, xs);
        stm::writeTVar<bsl::shared_ptr<List::list<bsl::pair<K, V> > > >(b,
                                                                        xs_);
        return v;
    }
    V stm_get_or(const K k, const V dflt) const
    {
        bsl::optional<V> v = this->stm_get(k);
        if (v.has_value()) {
            V x = *v;
            return x;
        }
        else {
            return dflt;
        }
    }
    void put(const K k, const V v) const
    {
        return stm::atomically([&] {
            return this->stm_put(k, v);
        });
    }
    bsl::optional<V> get(const K k) const
    {
        return stm::atomically([&] {
            return this->stm_get(k);
        });
    }
    bsl::optional<V> hash_delete(const K k) const
    {
        return stm::atomically([&] {
            return this->stm_delete(k);
        });
    }
    template <MapsTo<V, bsl::optional<V> > F1>
    V hash_update(const K k, F1&& f) const
    {
        return stm::atomically([&] {
            return this->stm_update(k, f);
        });
    }
    V get_or(const K k, const V dflt) const
    {
        return stm::atomically([&] {
            return this->stm_get_or(k, dflt);
        });
    }
    template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
    static bsl::optional<T2> assoc_lookup(
                   F0&&                                                    eqb,
                   const T1                                                k,
                   const bsl::shared_ptr<List::list<bsl::pair<T1, T2> > >& xs)
    {
        return bsl::visit(
             bdlf::Overloaded{
                 [&](const typename List::list<bsl::pair<T1, T2> >::nil _args)
                     -> bsl::optional<T2> {
                     return bsl::nullopt;
                 },
                 [&](const typename List::list<bsl::pair<T1, T2> >::cons _args)
                     -> bsl::optional<T2> {
                     bsl::pair<T1, T2> p = _args._a0;
                     bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > tl =
                         _args._a1;
                     T1 k_ = p.first;
                     T2 v  = p.second;
                     if (eqb(k, k_)) {
                         return bsl::make_optional<T2>(v);
                     }
                     else {
                         return assoc_lookup<T1, T2>(eqb, k, tl);
                     }
                 }},
             xs->v());
    }

    template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
    static bsl::shared_ptr<List::list<bsl::pair<T1, T2> > >
    assoc_insert_or_replace(
                   F0&&                                                    eqb,
                   const T1                                                k,
                   const T2                                                v,
                   const bsl::shared_ptr<List::list<bsl::pair<T1, T2> > >& xs)
    {
        return bsl::visit(
             bdlf::Overloaded{
                 [&](const typename List::list<bsl::pair<T1, T2> >::nil _args)
                     -> bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > {
                     return List::list<bsl::pair<T1, T2> >::ctor::cons_(
                         bsl::make_pair(k, v),
                         List::list<bsl::pair<T1, T2> >::ctor::nil_());
                 },
                 [&](const typename List::list<bsl::pair<T1, T2> >::cons _args)
                     -> bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > {
                     bsl::pair<T1, T2> p = _args._a0;
                     bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > tl =
                         _args._a1;
                     T1 k_ = p.first;
                     T2 v_ = p.second;
                     if (eqb(k, k_)) {
                         return List::list<bsl::pair<T1, T2> >::ctor::cons_(
                             bsl::make_pair(k, v),
                             tl);
                     }
                     else {
                         return List::list<bsl::pair<T1, T2> >::ctor::cons_(
                             bsl::make_pair(k_, v_),
                             assoc_insert_or_replace<T1, T2>(eqb, k, v, tl));
                     }
                 }},
             xs->v());
    }

    template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
    static bsl::pair<bsl::optional<T2>,
                     bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >
    assoc_remove(F0&&                                                    eqb,
                 const T1                                                k,
                 const bsl::shared_ptr<List::list<bsl::pair<T1, T2> > >& xs)
    {
        return bsl::visit(
             bdlf::Overloaded{
                 [&](const typename List::list<bsl::pair<T1, T2> >::nil _args)
                     -> bsl::pair<
                         bsl::optional<T2>,
                         bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > {
                     return bsl::make_pair(bsl::nullopt, xs);
                 },
                 [&](const typename List::list<bsl::pair<T1, T2> >::cons _args)
                     -> bsl::pair<
                         bsl::optional<T2>,
                         bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > {
                     bsl::pair<T1, T2> p = _args._a0;
                     bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > tl =
                         _args._a1;
                     T1 k_ = p.first;
                     T2 v_ = p.second;
                     if (eqb(k, k_)) {
                         return bsl::make_pair(bsl::make_optional<T2>(v_), tl);
                     }
                     else {
                         bsl::pair<
                             bsl::optional<T2>,
                             bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >
                             q = assoc_remove<T1, T2>(eqb, k, tl);
                         return bsl::make_pair(
                             q.first,
                             List::list<bsl::pair<T1, T2> >::ctor::cons_(
                                 bsl::make_pair(k_, v_),
                                 q.second));
                     }
                 }},
             xs->v());
    }

    template <typename T1, typename T2>
    static bsl::vector<bsl::shared_ptr<
        stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > > >
    mk_buckets(const int num)
    {
        bsl::vector<bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > > >
            buckets = {};
        bsl::function<bsl::vector<bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > > >(
                                                                 unsigned int)>
            f;
        f = [&](unsigned int n)
            -> bsl::vector<bsl::shared_ptr<stm::TVar<
                bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > > > {
            if (n <= 0) {
                return buckets;
            }
            else {
                unsigned int n_ = n - 1;
                bsl::shared_ptr<stm::TVar<
                    bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
                    b           = stm::atomically([&] {
                        return stm::newTVar<
                            bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(
                                 List::list<bsl::pair<T1, T2> >::ctor::nil_());
                    });
                buckets.push_back(b);
                return f(n_);
            }
        };
        return f(static_cast<unsigned int>(num));
    }

    template <typename T1,
              typename T2,
              MapsTo<bool, T1, T1> F0,
              MapsTo<int, T1>      F1>
    static bsl::shared_ptr<CHT<T1, T2> >
    new_hash(F0&& eqb, F1&& hash, const int requested)
    {
        int  n    = bsl::max(requested, 1);
        bsl::vector<bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > > >
             bs   = mk_buckets<T1, T2>(n);
        bool empt = bs.empty();
        if (empt) {
            bsl::shared_ptr<
                stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
                fb = stm::atomically([&] {
                    return stm::newTVar<
                        bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(
                                 List::list<bsl::pair<T1, T2> >::ctor::nil_());
                });
            bsl::vector<bsl::shared_ptr<stm::TVar<
                bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > > >
                v  = {};
            v.push_back(fb);
            return bsl::make_shared<CHT<T1, T2> >(
                                             CHT<T1, T2>{eqb, hash, v, 1, fb});
        }
        else {
            bsl::shared_ptr<
                stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
                b = bs.at(0);
            return bsl::make_shared<CHT<T1, T2> >(
                                             CHT<T1, T2>{eqb, hash, bs, n, b});
        }
    }
};
