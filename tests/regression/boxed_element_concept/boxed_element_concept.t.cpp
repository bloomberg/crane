#include <boxed_element_concept.h>

#include <cassert>

// The module satisfying the module type satisfies the concept it becomes:
// both spell the boxed element.
static_assert(FOREST<BoxedElementConcept::Forest>);

int main() {
  assert(BoxedElementConcept::total == 4u);
  return 0;
}
