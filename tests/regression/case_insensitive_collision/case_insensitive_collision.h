#ifndef INCLUDED_CASE_INSENSITIVE_COLLISION
#define INCLUDED_CASE_INSENSITIVE_COLLISION

#include <utility>

/// Crane capitalises an inductive's name to form its C++ type, so the
/// inductive bar and the definition Bar both want to be Bar.  The
/// generated code then has to say enum Bar to name the type at all, and the
/// two are indistinguishable at the use site.
struct CaseInsensitiveCollision {
  static inline const uint64_t foo = UINT64_C(1);
  static inline const uint64_t Foo = UINT64_C(2);
  enum class Bar { B1, B2 };

  template <typename T1> static T1 bar_rect(T1 f, T1 f0, Bar b) {
    switch (b) {
    case Bar::B1: {
      return f;
    }
    case Bar::B2: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 bar_rec(T1 f, T1 f0, Bar b) {
    switch (b) {
    case Bar::B1: {
      return f;
    }
    case Bar::B2: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t Bar0(Bar b);
  static inline const uint64_t run = ((foo + Foo) + Bar0(Bar::B2));
};

#endif // INCLUDED_CASE_INSENSITIVE_COLLISION
