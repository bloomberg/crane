#ifndef INCLUDED_EQ_RECT_TRANSPORT
#define INCLUDED_EQ_RECT_TRANSPORT

#include <cstdint>

struct EqRectTransport {
  template <typename T1, typename T2> static T2 cast(T1 a) { return a; }

  static constexpr uint64_t run = UINT64_C(5);
  using idty = uint64_t;
  static constexpr uint64_t run2 = UINT64_C(7);
};

#endif // INCLUDED_EQ_RECT_TRANSPORT
