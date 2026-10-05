#ifndef INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE
#define INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE

#include <stdexcept>
#include <utility>

enum class Unit;
enum class Bool0;
enum class Unit { TT };
enum class Bool0 { TRUE_, FALSE_ };

struct DependentElimStdexceptProbe {
  enum class Avail { PRESENT, ABSENT };

  template <typename T1> static T1 avail_rect(T1 f, T1 f0, Bool0, Avail a) {
    switch (a) {
    case Avail::PRESENT: {
      return f;
    }
    case Avail::ABSENT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 avail_rec(const T1 &f, const T1 &f0, Bool0 _x, Avail a) {
    return avail_rect<T1>(f, f0, _x, a);
  }

  static void get_present(Avail a);
  static constexpr Unit sample = Unit::TT;
};

#endif // INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE
