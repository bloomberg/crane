// Loopify + function-reference parameter: when a recursive function
// takes a predicate and is loopified, the continuation frame structs
// store the function with type F0 (the template parameter).  If F0
// deduces to a function reference type, std::move on the struct field
// yields a pointer that cannot bind back to the reference field in
// the next continuation struct.
//
// Reproduces the MSetAVL.MakeRaw.filter compile error from parse-a-lot:
//   error: non-const lvalue reference to type 'bool (const T &)'
//          cannot bind to a value of unrelated type '...*'

#include <loopify_filter_fn_ref.h>

#include <cassert>
#include <iostream>

int main() {
  auto result = LoopifyFilterFnRef::test_filter;
  (void)result;
  std::cout << "loopify_filter_fn_ref: passed" << std::endl;
  return 0;
}
