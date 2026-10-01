#include "instance_only_in_body_application.h"



Nat InstanceOnlyInBodyApplication::check(std::monostate){Sum<Nat,
Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>> r = runS<ParamsV<natIPtr>>(Nat::o());
if (std::holds_alternative<typename Sum<Nat,
Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>::Inl>(r.v_mut())) {
auto& [a0] = std::get<typename Sum<Nat,
Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>::Inl>(r.v_mut());
return a0;
} else {
auto& [a0] = std::get<typename Sum<Nat,
Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>::Inr>(r.v_mut());
return std::move(a0).template to_nat<ParamsV<natIPtr>>();
}}

