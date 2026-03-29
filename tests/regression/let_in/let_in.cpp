#include <let_in.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int LetIn::let_in_fun(const unsigned int n) {
  return (n + n);
}
