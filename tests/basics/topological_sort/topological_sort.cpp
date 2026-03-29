#include <topological_sort.h>

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> ListDef::seq(const unsigned int start,
                                                 const unsigned int len) {
  if (len <= 0) {
    return List<unsigned int>::nil();
  } else {
    unsigned int len0 = len - 1;
    return List<unsigned int>::cons(start, ListDef::seq((start + 1), len0));
  }
}
