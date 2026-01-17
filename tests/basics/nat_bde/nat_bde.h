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
    struct nat {
      public:
        struct O {
        };
        struct S {
            bsl::shared_ptr<nat> _a0;
        };
        using variant_t = bsl::variant<O, S>;
      private:
        variant_t v_;
        explicit nat(O x)
        : v_(bsl::move(x))
        {
        }
        explicit nat(S x)
        : v_(bsl::move(x))
        {
        }
      public:
        struct ctor {
            ctor() = delete;
            static bsl::shared_ptr<nat> O_()
            {
                return bsl::shared_ptr<nat>(new nat(O{}));
            }
            static bsl::shared_ptr<nat> S_(const bsl::shared_ptr<nat>& a0)
            {
                return bsl::shared_ptr<nat>(new nat(S{a0}));
            }
        };
        const variant_t& v() const { return v_; }
        int              nat_to_int() const
        {
            return bsl::visit(
                     bdlf::Overloaded{[&](const typename nat::O _args) -> int {
                                          return 0;
                                      },
                                      [&](const typename nat::S _args) -> int {
                                          bsl::shared_ptr<nat> n_ = _args._a0;
                                          return 1 + n_->nat_to_int();
                                      }},
                     this->v());
        }
        bsl::shared_ptr<nat> add(const bsl::shared_ptr<nat>& n) const
        {
            return bsl::visit(
                 bdlf::Overloaded{
                     [&](const typename nat::O _args) -> bsl::shared_ptr<nat> {
                         return n;
                     },
                     [&](const typename nat::S _args) -> bsl::shared_ptr<nat> {
                         bsl::shared_ptr<nat> x = _args._a0;
                         return nat::ctor::S_(x->add(n));
                     }},
                 this->v());
        }
        template <typename T1, MapsTo<T1, bsl::shared_ptr<nat>, T1> F1>
        T1 nat_rec(const T1 f, F1&& f0) const
        {
            return bsl::visit(
                      bdlf::Overloaded{[&](const typename nat::O _args) -> T1 {
                                           return f;
                                       },
                                       [&](const typename nat::S _args) -> T1 {
                                           bsl::shared_ptr<nat> n0 = _args._a0;
                                           return f0(n0, n0->nat_rec(f, f0));
                                       }},
                      this->v());
        }
        template <typename T1, MapsTo<T1, bsl::shared_ptr<nat>, T1> F1>
        T1 nat_rect(const T1 f, F1&& f0) const
        {
            return bsl::visit(
                      bdlf::Overloaded{[&](const typename nat::O _args) -> T1 {
                                           return f;
                                       },
                                       [&](const typename nat::S _args) -> T1 {
                                           bsl::shared_ptr<nat> n0 = _args._a0;
                                           return f0(n0, n0->nat_rect(f, f0));
                                       }},
                      this->v());
        }
    };
};
