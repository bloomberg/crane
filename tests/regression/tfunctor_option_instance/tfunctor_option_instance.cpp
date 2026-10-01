#include "tfunctor_option_instance.h"

TfunctorOptionInstance::box<crane::obj> TfunctorOptionInstance::TFunctor_box(
    crane::fn<crane::obj(crane::obj)> f,
    const TfunctorOptionInstance::box<crane::obj> &b) {
  return box<crane::obj>{f(b.unbox)};
}
