#ifndef INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE
#define INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE

#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Unit { e_TT };
enum class Bool0 { e_TRUE0, e_FALSE0 };

struct DependentElimStdexceptProbe {
  enum class Avail { e_PRESENT, e_ABSENT };

  template <typename T1>
  static T1 avail_rect(const T1 f, const T1 f0, const Bool0, const Avail a) {
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

  template <typename T1>
  static T1 avail_rec(const T1 f, const T1 f0, const Bool0, const Avail a) {
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

  static void get_present(const Avail a);
  static inline const Unit sample = []() {
    get_present(Avail::e_PRESENT);
    return Unit::e_TT;
  }();
};

#endif // INCLUDED_DEPENDENT_ELIM_STDEXCEPT_PROBE
