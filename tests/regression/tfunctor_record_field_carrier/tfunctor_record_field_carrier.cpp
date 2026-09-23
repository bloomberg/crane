#include "tfunctor_record_field_carrier.h"

template <typename _CraneTcArg>
using _crane_carrier_tc = std::optional<Exp<_CraneTcArg>>;
template <typename _CraneTcArg>
using _crane_carrier_tc1 = List<Exp<_CraneTcArg>>;

glob<std::any> TFunctor_glob(std::function<std::any(std::any)> f,
                             const glob<std::any> &g) {
  return glob<std::any>{
      f(g.g_name),
      tfmap<_crane_carrier_tc>(
          []() {
            return [](std::function<std::any(std::any)> _x0,
                      std::optional<Exp<std::any>> _x1)
                       -> std::optional<Exp<std::any>> {
              return TFunctor_option<Exp>(
                  [](auto &&_ec0, Exp<std::any> _ec1) {
                    return _ec1.TFunctor_exp(_ec0);
                  },
                  _x0, _x1);
            };
          }(),
          f, g.g_exp),
      tfmap<_crane_carrier_tc1>(
          []() {
            return [](std::function<std::any(std::any)> _x0,
                      List<Exp<std::any>> _x1) -> List<Exp<std::any>> {
              return TFunctor_list<Exp>(
                  [](auto &&_ec0, Exp<std::any> _ec1) {
                    return _ec1.TFunctor_exp(_ec0);
                  },
                  _x0, _x1);
            };
          }(),
          f, g.g_anns)};
}
