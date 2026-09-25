#include "itree_bind_binder_at_named_decl.h"



std::shared_ptr<ITree<Sum<Nat, Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>>> ItreeBindBinderAtNamedDecl::runM(){return runS<ParamsV<natIPtr>>();}
Nat ItreeBindBinderAtNamedDecl::to_natM(const Dval<typename ParamsV<natIPtr>::PTR::ptr, typename ParamsV<natIPtr>::IPTR::iptr>& d){return d.template to_nat<ParamsV<natIPtr>>();}std::shared_ptr<ITree<Nat>> ItreeBindBinderAtNamedDecl::check(){return itree_bind(runM(), [](const Sum<Nat, Dval<typename ParamsV<natIPtr>::PTR::ptr, typename ParamsV<natIPtr>::IPTR::iptr>>& r) {
return itree_ret([=]() mutable {
if (std::holds_alternative<typename Sum<Nat,
Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>::Inl>(r.v())) {
const auto& [a0] = std::get<typename Sum<Nat,
Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>::Inl>(r.v());
return a0;
} else {
const auto& [a0] = std::get<typename Sum<Nat,
Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>::Inr>(r.v());
return to_natM(a0);
}
}());
});}

