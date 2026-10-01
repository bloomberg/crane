#include "type_level_fun_apply.h"

TypeLevelFunApply::sem TypeLevelFunApply::app(const TypeLevelFunApply::ty &,
                                              const TypeLevelFunApply::ty &,
                                              TypeLevelFunApply::sem f,
                                              TypeLevelFunApply::sem x) {
  return crane::any_cast<crane::fn<crane::obj(crane::obj)>>(std::move(f))(
      std::move(x));
}
