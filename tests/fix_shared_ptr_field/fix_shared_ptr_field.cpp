#include "fix_shared_ptr_field.h"

FixSharedPtrField::wrapper
FixSharedPtrField::wrap_list(FixSharedPtrField::mylist l) {
  return wrapper::wrap(std::move(l));
}
