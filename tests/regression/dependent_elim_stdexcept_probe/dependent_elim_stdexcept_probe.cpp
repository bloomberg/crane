#include "dependent_elim_stdexcept_probe.h"

void DependentElimStdexceptProbe::get_present(
    DependentElimStdexceptProbe::Avail a) {
  {
    [&]() -> void {
      switch (a) {
      case Avail::PRESENT: {
        return;
      }
      case Avail::ABSENT: {
        throw std::logic_error("unreachable");
      }
      default:
        std::unreachable();
      }
    }();
    return;
  }
}
