#include "erased_dict_param_kept_at_use_site.h"

Nat ErasedDictParamKeptAtUseSite::go(const Nat &n) {
  return use<ParamsV<IPZ>>(n);
}
