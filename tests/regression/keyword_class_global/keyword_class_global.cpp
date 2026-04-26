#include <keyword_class_global.h>

#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) unsigned int
KeywordClassGlobal::class_(const unsigned int &n) {
  return (n + n);
}
