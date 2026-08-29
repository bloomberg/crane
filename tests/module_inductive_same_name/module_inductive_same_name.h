#ifndef INCLUDED_MODULE_INDUCTIVE_SAME_NAME
#define INCLUDED_MODULE_INDUCTIVE_SAME_NAME

#include <utility>

struct ModuleInductiveSameName {
  struct Color_Mod {
    enum class Color { R, G };

    template <typename T1> static T1 Color_rect(T1 f, T1 f0, Color c) {
      switch (c) {
      case Color::R: {
        return f;
      }
      case Color::G: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 Color_rec(T1 f, T1 f0, Color c) {
      switch (c) {
      case Color::R: {
        return f;
      }
      case Color::G: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    static uint64_t v(Color c);
  };

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_MODULE_INDUCTIVE_SAME_NAME
