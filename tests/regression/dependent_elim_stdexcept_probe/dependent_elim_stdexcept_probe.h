#ifndef INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE
#define INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE

#include <stdexcept>
#include <utility>

enum class Unit { TT };
enum class Bool0 { TRUE_, FALSE_ };

struct DependentElimStdexceptProbe {
  enum class Avail { PRESENT, ABSENT };

  template <typename T1> static T1 avail_rect(T1 f, T1 f0, Bool0, Avail a) {
    switch (a) {
    case Avail::PRESENT: {
      return f;
    } break;
    case Avail::ABSENT: {
      return f0;
    } break;
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 avail_rec(T1 f, T1 f0, Bool0, Avail a) {
    switch (a) {
    case Avail::PRESENT: {
      return f;
    } break;
    case Avail::ABSENT: {
      return f0;
    } break;
    default:
      std::unreachable();
    }
  }

  static void get_present(Avail a);
  static inline const Unit sample = []() {
    get_present(Avail::PRESENT);
    return Unit::TT;
  }();
};

#endif // INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE
