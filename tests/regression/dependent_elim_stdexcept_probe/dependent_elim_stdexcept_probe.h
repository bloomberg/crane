#ifndef INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE
#define INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE

#include <stdexcept>
#include <utility>

enum class Unit { e_TT };
enum class Bool0 { e_TRUE, e_FALSE };

struct DependentElimStdexceptProbe {
  enum class Avail { e_PRESENT, e_ABSENT };

  template <typename T1> static T1 avail_rect(T1 f, T1 f0, Bool0, Avail a) {
    switch (a) {
    case Avail::e_PRESENT: {
      return f;
    }
    case Avail::e_ABSENT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 avail_rec(T1 f, T1 f0, Bool0, Avail a) {
    switch (a) {
    case Avail::e_PRESENT: {
      return f;
    }
    case Avail::e_ABSENT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static void get_present(Avail a);
  static inline const Unit sample = []() {
    get_present(Avail::e_PRESENT);
    return Unit::e_TT;
  }();
};

#endif // INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE
