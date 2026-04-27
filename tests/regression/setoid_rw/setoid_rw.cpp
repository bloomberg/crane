#include <setoid_rw.h>

__attribute__((pure)) unsigned int SetoidRw::mod3(const unsigned int &n) {
  return (3u ? n % 3u : n);
}

__attribute__((pure)) unsigned int
SetoidRw::classify_mod3(const unsigned int &n) {
  auto _cs = mod3(n);
  if (_cs <= 0) {
    return 0u;
  } else {
    unsigned int n0 = _cs - 1;
    if (n0 <= 0) {
      return 1u;
    } else {
      unsigned int _x = n0 - 1;
      return 2u;
    }
  }
}

__attribute__((pure)) unsigned int SetoidRw::add_mod3(const unsigned int &x,
                                                      const unsigned int &y) {
  return mod3((x + y));
}
