#include <unit_monostate_erase.h>

#include <iostream>
#include <sstream>

int main() {
  using UME = UnitMonostateErase;

  // Example 1: seq_if — currently generates [&]() -> std::monostate { return; }
  // which is a type error (void return in monostate-returning lambda).
  // Should generate plain if control flow.
  UME::seq_if(true);
  UME::seq_if(false);

  // Example 2: seq_if_both — same monostate IIFE issue
  UME::seq_if_both(true);
  UME::seq_if_both(false);

  // Example 3: match_unit_tail — generates unnecessary IIFE wrapper
  UME::match_unit_tail(UME::Color::e_RED);
  UME::match_unit_tail(UME::Color::e_GREEN);
  UME::match_unit_tail(UME::Color::e_BLUE);

  // Example 4: match_then_next — unnecessary IIFE wrapper
  UME::match_then_next(UME::Color::e_RED);
  UME::match_then_next(UME::Color::e_GREEN);

  // Example 5: chained_ifs — two monostate IIFEs
  UME::chained_ifs(true, true);
  UME::chained_ifs(false, false);

  // Example 6: nested_matches — nested IIFEs
  UME::nested_matches(UME::Color::e_RED, UME::Color::e_RED);
  UME::nested_matches(UME::Color::e_GREEN, UME::Color::e_BLUE);

  std::cout << "All unit_monostate_erase tests passed!" << std::endl;
  return 0;
}
