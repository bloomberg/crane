#ifndef INCLUDED_MODULE_INDUCTIVE_SAME_NAME
#define INCLUDED_MODULE_INDUCTIVE_SAME_NAME

#include <utility>

struct ModuleInductiveSameName {
  /// A submodule containing an inductive of the same name.  A C++ member may
  /// not share its enclosing class's name, so the module is emitted as
  /// struct Color_Mod holding enum class Color.
  struct Color_Mod {
    /// A submodule containing an inductive of the same name.  A C++ member may
    /// not share its enclosing class's name, so the module is emitted as
    /// struct Color_Mod holding enum class Color.
    enum class Color0 { R, G };

    template <typename T1> static T1 Color_rect(T1 f, T1 f0, Color0 c) {
      switch (c) {
      case Color0::R: {
        return f;
      }
      case Color0::G: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 Color_rec(T1 f, T1 f0, Color0 c) {
      switch (c) {
      case Color0::R: {
        return f;
      }
      case Color0::G: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    static uint64_t v(Color0 c);
  };

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_MODULE_INDUCTIVE_SAME_NAME
