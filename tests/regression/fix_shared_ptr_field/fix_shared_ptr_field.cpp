#include <fix_shared_ptr_field.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Dummy use of wrapper to keep it alive for extraction.
std::shared_ptr<FixSharedPtrField::wrapper>
FixSharedPtrField::wrap_list(std::shared_ptr<FixSharedPtrField::mylist> l) {
  return wrapper::wrap(l);
}
