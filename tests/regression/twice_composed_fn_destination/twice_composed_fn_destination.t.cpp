#include <twice_composed_fn_destination.h>
#include <iostream>
int main() {
  std::cout << TwiceComposedFnDestination::result << std::endl;
  return TwiceComposedFnDestination::result == 20 ? 0 : 1;
}
