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
#include <nat_bde.h>

namespace BloombergLP {

}
bsl::shared_ptr<Nat::nat> Nat::add(const bsl::shared_ptr<Nat::nat>& m,
                                   const bsl::shared_ptr<Nat::nat>& n)
{
    return bsl::visit(
                  bdlf::Overloaded{[&](const typename Nat::nat::O _args)
                                       -> bsl::shared_ptr<Nat::nat> {
                                       return n;
                                   },
                                   [&](const typename Nat::nat::S _args)
                                       -> bsl::shared_ptr<Nat::nat> {
                                       bsl::shared_ptr<Nat::nat> x = _args._a0;
                                       return nat::ctor::S_(x->add(n));
                                   }},
                  m->v());
}

int Nat::nat_to_int(const bsl::shared_ptr<Nat::nat>& n)
{
    return bsl::visit(
                bdlf::Overloaded{[&](const typename Nat::nat::O _args) -> int {
                                     return 0;
                                 },
                                 [&](const typename Nat::nat::S _args) -> int {
                                     bsl::shared_ptr<Nat::nat> n_ = _args._a0;
                                     return 1 + n_->nat_to_int();
                                 }},
                n->v());
}
