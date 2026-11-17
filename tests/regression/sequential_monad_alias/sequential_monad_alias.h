#ifndef INCLUDED_SEQUENTIAL_MONAD_ALIAS
#define INCLUDED_SEQUENTIAL_MONAD_ALIAS

#include <iostream>
#include <string>
#include <variant>

struct SequentialMonadAlias {
  static void aliased();
  static void direct();
  static void both();
  static void twice(const std::monostate &m);
};

#endif // INCLUDED_SEQUENTIAL_MONAD_ALIAS
