#include "type_level_fun_apply.h"

TypeLevelFunApply::sem TypeLevelFunApply::app(const TypeLevelFunApply::ty &,
                                              const TypeLevelFunApply::ty &,
                                              TypeLevelFunApply::sem f,
                                              TypeLevelFunApply::sem x) {
  return std::any_cast<std::function<std::any(std::any)>>(f)(x);
}
