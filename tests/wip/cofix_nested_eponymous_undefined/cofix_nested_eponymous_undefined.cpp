#include "cofix_nested_eponymous_undefined.h"

uint64_t CofixNestedEponymousUndefined::third_of(uint64_t n) {
  return Stream::from(n).tl().tl().hd();
}
