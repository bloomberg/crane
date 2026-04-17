#include <dependent_elim_stdexcept_probe.h>

#include <type_traits>
#include <utility>

void DependentElimStdexceptProbe::get_present(
    const DependentElimStdexceptProbe::Avail a) {
  {
    [&]() -> void {
      switch (a) {
      case Avail::e_PRESENT: {
        return;
      }
      case Avail::e_ABSENT: {
        throw std::logic_error("unreachable");
      }
      default:
        std::unreachable();
      }
    }();
    return;
  }
}
