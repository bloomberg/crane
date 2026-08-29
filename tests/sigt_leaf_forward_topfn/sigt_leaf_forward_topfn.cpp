#include "sigt_leaf_forward_topfn.h"

bool wrap_string(const std::string &s) { return (s == s); }

domty garg(uint64_t n) {
  if (n <= 0) {
    return std::make_pair(
        std::any(std::string(1, (static_cast<char>(
                                    (false ? 1 : 0) | (false ? 2 : 0) |
                                    (false ? 4 : 0) | (true ? 8 : 0) |
                                    (false ? 16 : 0) | (true ? 32 : 0) |
                                    (true ? 64 : 0) | (false ? 128 : 0)))) +
                 std::string(1, (static_cast<char>(
                                    (true ? 1 : 0) | (false ? 2 : 0) |
                                    (false ? 4 : 0) | (true ? 8 : 0) |
                                    (false ? 16 : 0) | (true ? 32 : 0) |
                                    (true ? 64 : 0) | (false ? 128 : 0)))) +
                 std::string()),
        std::any(std::monostate{}));
  } else {
    uint64_t _x = n - 1;
    return std::make_pair(std::any(UINT64_C(0)), std::any(std::monostate{}));
  }
}

bool run(const SigT<std::pair<uint64_t, List<uint64_t>>,
                    std::pair<std::any, std::any>> &e) {
  const auto &[x0, a1] = e;
  const auto &[n, _x] = x0;
  const auto &[f, _x0] = std::any_cast<std::pair<std::any, std::any>>(a1);
  if (std::any_cast<bool>(
          std::any_cast<std::function<std::any(std::any)>>(f)(garg(n)))) {
    return true;
  } else {
    return false;
  }
}

bool check(std::monostate) { return run(my_entry); }
