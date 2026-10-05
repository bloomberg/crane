#include "mixed_class_dict_carrier_crossed.h"

modu<crane::obj> TFunctor_modu(TFunctor<Exp<crane::obj>> h, Endo<Nat> h0,
                               TFunctor<Decl<crane::obj>> h1,
                               const crane::fn<crane::obj(crane::obj)> &f,
                               const modu<crane::obj> &m) {
  return modu<crane::obj>{
      endo<Nat>(std::move(h0), m.m_tag),
      tfmap<List<Exp<crane::obj>>, crane::obj, crane::obj>(
          [=]() {
            return [=](crane::fn<crane::obj(crane::obj)> _x0,
                       const auto &_x1) -> List<Exp<crane::obj>> {
              return TFunctor_list<Exp<crane::obj>>(
                  h, _x0, crane_convert<List<Exp<crane::obj>>>(_x1));
            };
          }(),
          f, m.m_exps),
      tfmap<List<Decl<crane::obj>>, crane::obj, crane::obj>(
          [=]() {
            return [=](crane::fn<crane::obj(crane::obj)> _x0,
                       const auto &_x1) -> List<Decl<crane::obj>> {
              return TFunctor_list<Decl<crane::obj>>(
                  h1, _x0, crane_convert<List<Decl<crane::obj>>>(_x1));
            };
          }(),
          f, m.m_decls)};
}
