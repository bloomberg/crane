#ifndef INCLUDED_MODULE_INDUCTIVE_SAME_NAME
#define INCLUDED_MODULE_INDUCTIVE_SAME_NAME

struct ModuleInductiveSameName {
  /// A submodule containing an inductive of the same name.  A C++ member may
  /// not share its enclosing class's name, so the module is emitted as
  /// struct Color_Mod holding enum class Color.
  struct Color {
    /// A submodule containing an inductive of the same name.  A C++ member may
    /// not share its enclosing class's name, so the module is emitted as
    /// struct Color_Mod holding enum class Color.
    enum class Color { R, G };
  };

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_MODULE_INDUCTIVE_SAME_NAME
