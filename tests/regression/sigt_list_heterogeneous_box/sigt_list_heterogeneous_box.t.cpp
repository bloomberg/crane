#include <sigt_list_heterogeneous_box.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::S>(SigtListHeterogeneousBox::run.v()));
  return 0;
}
