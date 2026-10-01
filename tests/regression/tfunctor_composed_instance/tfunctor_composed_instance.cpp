#include "tfunctor_composed_instance.h"

List<crane::obj>
TfunctorComposedInstance::TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                                        const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(std::move(x0_));
}

TfunctorComposedInstance::box<crane::obj>
TfunctorComposedInstance::TFunctor_box(
    crane::fn<crane::obj(crane::obj)> f,
    const TfunctorComposedInstance::box<crane::obj> &b) {
  return box<crane::obj>{f(b.unbox)};
}
