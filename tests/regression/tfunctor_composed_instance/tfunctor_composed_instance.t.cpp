#include <tfunctor_composed_instance.h>

#include <cassert>
#include <iostream>

int main() {
  // tfmap S over [Box 1; Box 2] through TFunctor_list' gives [Box 2; Box 3].
  assert(TfunctorComposedInstance::is_five);
  std::cout << "tfunctor_composed_instance: ok" << std::endl;
  return 0;
}
