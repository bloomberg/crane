#include "global_arrays.h"

#include <iostream>
#include <variant>
#include <vector>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

std::vector<uint64_t> to_vector(const List<uint64_t> &l) {
  std::vector<uint64_t> out;
  const List<uint64_t> *cur = &l;
  while (auto *c = std::get_if<List<uint64_t>::Cons>(&cur->v())) {
    out.push_back(c->a);
    cur = c->l.get();
  }
  return out;
}

List<uint64_t> of_vector(const std::vector<uint64_t> &v) {
  List<uint64_t> l = List<uint64_t>::nil();
  for (auto it = v.rbegin(); it != v.rend(); ++it)
    l = List<uint64_t>::cons(*it, std::move(l));
  return l;
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // new_array, write_array, array_to_list
  {
    auto result = to_vector(GlobalArrays::squares(5));
    ASSERT((result == std::vector<uint64_t>{0, 1, 4, 9, 16}));
    std::cout << "squares 5: " << result.size() << " elements" << std::endl;
  }
  {
    auto result = to_vector(GlobalArrays::squares(0));
    ASSERT(result.empty());
  }

  // array_of_list, read_array
  {
    auto result = GlobalArrays::sum_list(of_vector({3, 1, 4, 1, 5}));
    ASSERT(result == 14);
    std::cout << "sum_list [3;1;4;1;5]: " << result << std::endl;
  }

  // swap_array
  {
    auto result = to_vector(GlobalArrays::swap_ends(of_vector({1, 2, 3, 4})));
    ASSERT((result == std::vector<uint64_t>{4, 2, 3, 1}));
    std::cout << "swap_ends [1;2;3;4]: [" << result[0] << ", " << result[1]
              << ", " << result[2] << ", " << result[3] << "]" << std::endl;
  }

  // new_array default, write_array then read_array
  {
    auto result = GlobalArrays::write_then_read();
    ASSERT(result.first == 42);
    ASSERT(result.second == 7);
    std::cout << "write_then_read: (" << result.first << ", " << result.second
              << ")" << std::endl;
  }

  // arrays and references together
  {
    auto result = GlobalArrays::array_then_ref();
    ASSERT(result == 14);
    std::cout << "array_then_ref: " << result << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll global_arrays tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
