#include "mixed_class_dict_carrier_crossed.h"

template <typename _CraneTcArg>
using _crane_carrier_tc_ff1db37af57fd729 = List<Exp<_CraneTcArg>>;
template <typename _CraneTcArg>
using _crane_carrier_tc_842249e3b6c0e453 = List<Decl<_CraneTcArg>>;

modu<std::any> TFunctor_modu(std::type_identity_t<TFunctor<Exp>> h,
                             Endo<Nat> h0,
                             std::type_identity_t<TFunctor<Decl>> h1,
                             std::function<std::any(std::any)> f,
                             const modu<std::any> &m) {
  return modu<std::any>{
      endo<Nat>(std::move(h0), m.m_tag),
      tfmap<_crane_carrier_tc_ff1db37af57fd729>(
          [=]() mutable {
            return [=](std::function<std::any(std::any)> _x0,
                       List<Exp<std::any>> _x1) mutable -> List<Exp<std::any>> {
              return TFunctor_list<Exp>(h, _x0, _x1);
            };
          }(),
          f, m.m_exps),
      tfmap<_crane_carrier_tc_842249e3b6c0e453>(
          [=]() mutable {
            return
                [=](std::function<std::any(std::any)> _x0,
                    List<Decl<std::any>> _x1) mutable -> List<Decl<std::any>> {
                  return TFunctor_list<Decl>(h1, _x0, _x1);
                };
          }(),
          f, m.m_decls)};
}
