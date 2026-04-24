#include <todo_extract_constant_noninline.h>

#include <todo_extract_constant_noninline_support.h>
#include <type_traits>

__attribute__((pure)) unsigned int
TodoExtractConstantNoninline::foreign_inc(const unsigned int &_x0) {
  return foreign_inc_impl(_x0);
}
