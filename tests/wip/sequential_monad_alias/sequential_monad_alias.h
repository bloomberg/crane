#ifndef INCLUDED_SEQUENTIAL_MONAD_ALIAS
#define INCLUDED_SEQUENTIAL_MONAD_ALIAS

#include <crane_itree.h>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <variant>

struct SequentialMonadAlias {
  static inline const IOt<std::monostate> aliased =
      std::cout << std::string("aliased") << '\n';
  static void direct();
  static inline const IOt<std::monostate> both = []() {
    aliased;
    return direct();
  }();
  static IOt<std::monostate> twice(const std::monostate &m);
};

#endif // INCLUDED_SEQUENTIAL_MONAD_ALIAS
