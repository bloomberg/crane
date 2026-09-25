#include "erased_dval_in_container.h"



Nat ErasedDvalInContainer::s0(const List<Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>>& x0_){return sum_list<ParamsV<natIPtr>>(x0_);}
std::optional<List<Dval<typename ParamsV<natIPtr>::PTR::ptr, typename ParamsV<natIPtr>::IPTR::iptr>>> ErasedDvalInContainer::w0(const Dval<typename ParamsV<natIPtr>::PTR::ptr,
typename ParamsV<natIPtr>::IPTR::iptr>& x0_){return x0_.template wrap<ParamsV<natIPtr>>();}

