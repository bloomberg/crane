#include "dependent_elim_stdexcept_probe.h"

void DependentElimStdexceptProbe::get_present(
    DependentElimStdexceptProbe::Avail a) {
  {
    [&]() -> void {
      switch (a) {
      case Avail::PRESENT: {
        return;
      } break;
      case Avail::ABSENT: {
        throw std::logic_error("unreachable");
      } break;
      default:
        std::unreachable();
      }
    }();
    return;
  }
}
