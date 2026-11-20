#include <typed_mapping_exact_numbers.h>

#include <boost/multiprecision/cpp_int.hpp>
#include <cassert>
#include <type_traits>

using boost::multiprecision::cpp_int;

// A read-only parameter of a type that duplicates its value is passed by
// const reference.
static_assert(std::is_same_v<decltype(&TypedMappingExactNumbers::predecessor),
                             cpp_int (*)(const cpp_int &)>);

int main() {
  // 25! does not fit in 64 bits.
  assert(TypedMappingExactNumbers::factorial(cpp_int(25)) ==
         cpp_int("15511210043330985984000000"));
  assert(TypedMappingExactNumbers::big == cpp_int("100000000000000000000"));
  assert(!TypedMappingExactNumbers::exceeds_big(cpp_int(5)));
  assert(TypedMappingExactNumbers::exceeds_big(TypedMappingExactNumbers::factorial(cpp_int(25))));
  assert(TypedMappingExactNumbers::predecessor(cpp_int(0)) == 0);
  assert(TypedMappingExactNumbers::predecessor(TypedMappingExactNumbers::big) ==
         cpp_int("99999999999999999999"));
  assert(TypedMappingExactNumbers::sum3(cpp_int(1), cpp_int(2), TypedMappingExactNumbers::big) ==
         cpp_int("100000000000000000003"));
  return 0;
}
