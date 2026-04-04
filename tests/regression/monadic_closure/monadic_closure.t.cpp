#include <monadic_closure.h>

using namespace std::string_literals;

int main() {
  // Test 2: apply_after_effect
  // Would need stdin, skip for compilation test

  // Test 4: with_length
  // Would need stdin, skip for compilation test

  // Test 6: count_matching (pure, no IO needed)
  auto r = MonadicClosure::count_matching(
    [](const std::string& s) { return s.empty(); },
    List<std::string>::cons("a"s,
      List<std::string>::cons(""s,
        List<std::string>::cons("bc"s, List<std::string>::nil())))
  );

  return 0;
}
