#include "tfunctor_list_of_triples.h"

List<crane::obj>
TfunctorListOfTriples::TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                                     const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(std::move(x0_));
}

TfunctorListOfTriples::phi<crane::obj> TfunctorListOfTriples::TFunctor_phi(
    crane::fn<crane::obj(crane::obj)> f,
    const TfunctorListOfTriples::phi<crane::obj> &p) {
  const auto &[t0] = p;
  return phi<crane::obj>::phi0(crane_call_erased(std::move(f), t0));
}

TfunctorListOfTriples::metadata<crane::obj> TfunctorListOfTriples::TFunctor_md(
    crane::fn<crane::obj(crane::obj)> f,
    const TfunctorListOfTriples::metadata<crane::obj> &p) {
  const auto &[t0] = p;
  return metadata<crane::obj>::md(crane_call_erased(std::move(f), t0));
}

TfunctorListOfTriples::block<crane::obj> TfunctorListOfTriples::TFunctor_block(
    crane::fn<crane::obj(crane::obj)> f,
    const TfunctorListOfTriples::block<crane::obj> &b) {
  return block<crane::obj>{tfmap<
      List<crane::obj>,
      std::pair<std::pair<Nat, TfunctorListOfTriples::phi<crane::obj>>,
                List<TfunctorListOfTriples::metadata<crane::obj>>>,
      std::pair<std::pair<Nat, TfunctorListOfTriples::phi<crane::obj>>,
                List<TfunctorListOfTriples::metadata<crane::obj>>>>(
      [](auto &&_ec0, List<crane::obj> _ec1) {
        return TFunctor_list(_ec0, _ec1);
      },
      [=](const std::pair<
          std::pair<Nat, TfunctorListOfTriples::phi<crane::obj>>,
          List<TfunctorListOfTriples::metadata<crane::obj>>> &pat) {
        const auto &[y, md] = pat;
        const auto &[id, p] = y;
        return std::make_pair(
            std::make_pair(id,
                           tfmap<TfunctorListOfTriples::phi<crane::obj>,
                                 crane::obj, crane::obj>(
                               [](auto &&_ec0,
                                  TfunctorListOfTriples::phi<crane::obj> _ec1) {
                                 return TFunctor_phi(_ec0, _ec1);
                               },
                               f, p)),
            tfmap<List<TfunctorListOfTriples::metadata<crane::obj>>, crane::obj,
                  crane::obj>(
                []() {
                  return [](crane::fn<crane::obj(crane::obj)> _x0,
                            const auto &_x1)
                             -> List<
                                 TfunctorListOfTriples::metadata<crane::obj>> {
                    return TFunctor_list_<
                        TfunctorListOfTriples::metadata<crane::obj>>(
                        [](auto &&_ec0,
                           TfunctorListOfTriples::metadata<crane::obj> _ec1) {
                          return TFunctor_md(_ec0, _ec1);
                        },
                        _x0,
                        crane_convert<
                            List<TfunctorListOfTriples::metadata<crane::obj>>>(
                            _x1));
                  };
                }(),
                f, md));
      },
      b.blk_phis)};
}
