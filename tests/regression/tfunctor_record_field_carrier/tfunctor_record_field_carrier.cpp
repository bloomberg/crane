#include "tfunctor_record_field_carrier.h"

glob<crane::obj> TFunctor_glob(crane::fn<crane::obj(crane::obj)> f,
                               const glob<crane::obj> &g) {
  return glob<crane::obj>{
      f(g.g_name),
      tfmap<std::optional<Exp<crane::obj>>, crane::obj, crane::obj>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0,
                      const auto &_x1) -> std::optional<Exp<crane::obj>> {
              return TFunctor_option<Exp<crane::obj>>(
                  [](auto &&_ec0, Exp<crane::obj> _ec1) {
                    return _ec1.TFunctor_exp(_ec0);
                  },
                  _x0, crane_convert<std::optional<Exp<crane::obj>>>(_x1));
            };
          }(),
          f, g.g_exp),
      tfmap<List<Exp<crane::obj>>, crane::obj, crane::obj>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0,
                      const auto &_x1) -> List<Exp<crane::obj>> {
              return TFunctor_list<Exp<crane::obj>>(
                  [](auto &&_ec0, Exp<crane::obj> _ec1) {
                    return _ec1.TFunctor_exp(_ec0);
                  },
                  _x0, crane_convert<List<Exp<crane::obj>>>(_x1));
            };
          }(),
          f, g.g_anns)};
}
