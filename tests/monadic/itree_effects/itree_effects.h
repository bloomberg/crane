#ifndef INCLUDED_ITREE_EFFECTS
#define INCLUDED_ITREE_EFFECTS

#include <cstdlib>
#include <ctime>
#include <iostream>
#include <string>
#include <variant>

using namespace std::string_literals;

/// ------------------------------------------------------------------
struct ITreeEffects {
  static void greet();
  static uint64_t roll_dice(uint64_t sides);
  static void timed_greeting();
  static void echo_loop(uint64_t n);
};

#endif // INCLUDED_ITREE_EFFECTS
