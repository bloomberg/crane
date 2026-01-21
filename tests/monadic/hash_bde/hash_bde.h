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
            A                         _a0;
            bsl::shared_ptr<list<A> > _a1;
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
            static bsl::shared_ptr<list<A> > nil_()
            {
                return bsl::shared_ptr<list<A> >(new list<A>(nil{}));
            }
            static bsl::shared_ptr<list<A> > cons_(
                                           A                                a0,
                                           const bsl::shared_ptr<list<A> >& a1)
            {
                return bsl::shared_ptr<list<A> >(new list<A>(cons{a0, a1}));
            }
        };
        const variant_t& v() const { return v_; }
    };
};

struct Vector_axioms {
};

struct STM {
};

struct TVar {
    struct TVar_axioms {
    };
};

struct CHT {
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
    };

    template <typename T1, typename T2>
    static bool cht_eqb(const bsl::shared_ptr<CHT<T1, T2> >& c,
                        const T1                             _x0,
                        const bsl::shared_ptr<CHT<T1, T2> >& _x1)
    {
        return _x1->cht_eqb(_x0, _x1);
    }

    template <typename T1, typename T2>
    static int cht_hash(const bsl::shared_ptr<CHT<T1, T2> >& c,
                        const bsl::shared_ptr<CHT<T1, T2> >& _x0)
    {
        return _x0->cht_hash(_x0);
    }

    template <typename T1, typename T2>
    static bsl::vector<bsl::shared_ptr<
        stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > > >
    cht_buckets(const bsl::shared_ptr<CHT<T1, T2> >& c)
    {
        return c->cht_buckets;
    }

    template <typename T1, typename T2>
    static int cht_nbuckets(const bsl::shared_ptr<CHT<T1, T2> >& c)
    {
        return c->cht_nbuckets;
    }

    template <typename T1, typename T2>
    static bsl::shared_ptr<
        stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
    cht_fallback(const bsl::shared_ptr<CHT<T1, T2> >& c)
    {
        return c->cht_fallback;
    }

    template <typename T1, typename T2>
    static bsl::shared_ptr<
        stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
    bucket_of(const bsl::shared_ptr<CHT<T1, T2> >& t, const T1 k)
    {
        int i = t->cht_hash(k) % t->cht_nbuckets;
        return t->cht_buckets.at(i);
    }

    template <typename T1, typename T2>
    static bsl::optional<T2> stm_get(const bsl::shared_ptr<CHT<T1, T2> >& t,
                                     const T1                             k)
    {
        bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
            b = bucket_of<T1, T2>(t, k);
        bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > xs =
              stm::readTVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(
                  b);
        return assoc_lookup<T1, T2>(t->cht_eqb, k, xs);
    }

    template <typename T1, typename T2>
    static void stm_put(const bsl::shared_ptr<CHT<T1, T2> >& t,
                        const T1                             k,
                        const T2                             v)
    {
        bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
            b = bucket_of<T1, T2>(t, k);
        bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > xs =
              stm::readTVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(
                  b);
        bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > xs_ =
                         assoc_insert_or_replace<T1, T2>(t->cht_eqb, k, v, xs);
        stm::writeTVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(b,
                                                                          xs_);
        return;
    }

    template <typename T1, typename T2>
    static bsl::optional<T2> stm_delete(const bsl::shared_ptr<CHT<T1, T2> >& t,
                                        const T1                             k)
    {
        bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
            b = bucket_of<T1, T2>(t, k);
        bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > xs =
              stm::readTVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(
                  b);
        bsl::pair<bsl::optional<T2>,
                  bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >
            p = assoc_remove<T1, T2>(t->cht_eqb, k, xs);
        if (p.first.has_value()) {
            T2 _x = *p.first;
            stm::writeTVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(
                                                                     b,
                                                                     p.second);
            return p.first;
        }
        else {
            return p.first;
        }
    }

    template <typename T1, typename T2, MapsTo<T2, bsl::optional<T2> > F2>
    static T2 stm_update(const bsl::shared_ptr<CHT<T1, T2> >& t,
                         const T1                             k,
                         F2&&                                 f)
    {
        bsl::shared_ptr<
            stm::TVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > > >
            b = bucket_of<T1, T2>(t, k);
        bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > xs =
              stm::readTVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(
                  b);
        bsl::optional<T2> ov = assoc_lookup<T1, T2>(t->cht_eqb, k, xs);
        T2                v  = f(ov);
        bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > xs_ =
                         assoc_insert_or_replace<T1, T2>(t->cht_eqb, k, v, xs);
        stm::writeTVar<bsl::shared_ptr<List::list<bsl::pair<T1, T2> > > >(b,
                                                                          xs_);
        return v;
    }

    template <typename T1, typename T2>
    static T2 stm_get_or(const bsl::shared_ptr<CHT<T1, T2> >& t,
                         const T1                             k,
                         const T2                             dflt)
    {
        bsl::optional<T2> v = stm_get<T1, T2>(t, k);
        if (v.has_value()) {
            T2 x = *v;
            return x;
        }
        else {
            return dflt;
        }
    }

    static int max(const int a, const int b);

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
        int  n    = max(requested, 1);
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

    template <typename T1, typename T2>
    static void put(const bsl::shared_ptr<CHT<T1, T2> >& t,
                    const T1                             k,
                    const T2                             v)
    {
        return stm::atomically([&] {
            return stm_put<T1, T2>(t, k, v);
        });
    }

    template <typename T1, typename T2>
    static bsl::optional<T2> get(const bsl::shared_ptr<CHT<T1, T2> >& t,
                                 const T1                             k)
    {
        return stm::atomically([&] {
            return stm_get<T1, T2>(t, k);
        });
    }

    template <typename T1, typename T2>
    static bsl::optional<T2> hash_delete(
                                        const bsl::shared_ptr<CHT<T1, T2> >& t,
                                        const T1                             k)
    {
        return stm::atomically([&] {
            return stm_delete<T1, T2>(t, k);
        });
    }

    template <typename T1, typename T2, MapsTo<T2, bsl::optional<T2> > F2>
    static T2 hash_update(const bsl::shared_ptr<CHT<T1, T2> >& t,
                          const T1                             k,
                          F2&&                                 f)
    {
        return stm::atomically([&] {
            return stm_update<T1, T2>(t, k, f);
        });
    }

    template <typename T1, typename T2>
    static T2 get_or(const bsl::shared_ptr<CHT<T1, T2> >& t,
                     const T1                             k,
                     const T2                             dflt)
    {
        return stm::atomically([&] {
            return stm_get_or<T1, T2>(t, k, dflt);
        });
    }
};
