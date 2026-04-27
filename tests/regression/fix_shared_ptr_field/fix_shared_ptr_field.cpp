#include <fix_shared_ptr_field.h>

/// Dummy use of wrapper to keep it alive for extraction.
__attribute__((pure)) FixSharedPtrField::wrapper
FixSharedPtrField::wrap_list(FixSharedPtrField::mylist l) {
  return wrapper::wrap(l);
}
