#include <bdlf_overloaded.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>

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

struct Nat {
    struct Nat {
        struct O;
        struct S;
        using nat = bsl::variant<O, S>;
        struct O {
            static bsl::shared_ptr<nat> make();
        };
        struct S {
            bsl::shared_ptr<nat> _a0;
            static bsl::shared_ptr<nat> make(bsl::shared_ptr<nat> _a0);
        };
    };

    template <typename T1,
              MapsTo<T1, bsl::shared_ptr<typename Nat::nat>, T1> F1>
    T1
    nat_rect(const T1 f, F1&& f0, const bsl::shared_ptr<typename Nat::nat> n)
    {
        return bsl::visit(
                     bdlf::Overloaded{
                         [&](const typename Nat::O _args) -> T1 {
                             return f;
                         },
                         [&](const typename Nat::S _args) -> T1 {
                             bsl::shared_ptr<typename Nat::nat> n0 = _args._a0;
                             return f0(n0, nat_rect<T1>(f, f0, n0));
                         }},
                     *n);
    }

    template <typename T1,
              MapsTo<T1, bsl::shared_ptr<typename Nat::nat>, T1> F1>
    T1 nat_rec(const T1 f, F1&& f0, const bsl::shared_ptr<typename Nat::nat> n)
    {
        return bsl::visit(
                     bdlf::Overloaded{
                         [&](const typename Nat::O _args) -> T1 {
                             return f;
                         },
                         [&](const typename Nat::S _args) -> T1 {
                             bsl::shared_ptr<typename Nat::nat> n0 = _args._a0;
                             return f0(n0, nat_rec<T1>(f, f0, n0));
                         }},
                     *n);
    }

    static bsl::shared_ptr<typename Nat::nat> add(
                                   const bsl::shared_ptr<typename Nat::nat> m,
                                   const bsl::shared_ptr<typename Nat::nat> n);

    static int nat_to_int(const bsl::shared_ptr<typename Nat::nat> n);
};
