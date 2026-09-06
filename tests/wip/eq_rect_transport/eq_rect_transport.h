#ifndef INCLUDED_EQ_RECT_TRANSPORT
#define INCLUDED_EQ_RECT_TRANSPORT

struct EqRectTransport {
  template <typename T1, typename T2> static T2 cast(T1 a) { return a; }

  static inline const uint64_t run = cast<uint64_t, uint64_t>(UINT64_C(5));
  static inline const uint64_t run2 = cast<idty, uint64_t>(UINT64_C(7));
};

#endif // INCLUDED_EQ_RECT_TRANSPORT
