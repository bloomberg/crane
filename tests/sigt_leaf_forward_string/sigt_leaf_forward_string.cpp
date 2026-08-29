#include "sigt_leaf_forward_string.h"

Inst::sem my_arg(std::monostate) {
  return std::string(1,
                     (static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                        (false ? 4 : 0) | (true ? 8 : 0) |
                                        (false ? 16 : 0) | (true ? 32 : 0) |
                                        (true ? 64 : 0) | (false ? 128 : 0)))) +
         std::string(1,
                     (static_cast<char>((true ? 1 : 0) | (false ? 2 : 0) |
                                        (false ? 4 : 0) | (true ? 8 : 0) |
                                        (false ? 16 : 0) | (true ? 32 : 0) |
                                        (true ? 64 : 0) | (false ? 128 : 0)))) +
         std::string();
}

bool check(std::monostate) { return M::run(my_entry, my_arg); }
