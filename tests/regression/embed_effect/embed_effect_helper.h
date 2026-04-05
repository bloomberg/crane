// Helper for embed_effect regression test.
// Provides stub implementations for the custom-extracted bugE events.

#ifndef INCLUDED_EMBED_EFFECT_HELPER
#define INCLUDED_EMBED_EFFECT_HELPER

#include <cstdint>
#include <string>

inline int &get_create_count() {
  static int n = 0;
  return n;
}
inline int &get_read_count() {
  static int n = 0;
  return n;
}

inline void bug_create_impl(const std::string &) { ++get_create_count(); }

inline int64_t bug_read_impl() {
  ++get_read_count();
  return 42;
}

#endif // INCLUDED_EMBED_EFFECT_HELPER
