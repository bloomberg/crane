#include <fix_shared_ptr_field.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Dummy use of wrapper to keep it alive for extraction.
__attribute__((pure)) FixSharedPtrField::wrapper
FixSharedPtrField::wrap_list(FixSharedPtrField::mylist l) {
  return wrapper::wrap(l);
}
