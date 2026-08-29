#ifndef INCLUDED_MODULE_INDUCTIVE_SAME_NAME
#define INCLUDED_MODULE_INDUCTIVE_SAME_NAME

struct ModuleInductiveSameName {
  /// A submodule containing an inductive of the same name.  Both become C++
  /// members named Color inside the enclosing struct: member 'Color' has
  /// the same name as its class.
  struct Color {
    /// A submodule containing an inductive of the same name.  Both become C++
    /// members named Color inside the enclosing struct: member 'Color' has
    /// the same name as its class.
    enum class Color { R, G };
  };

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_MODULE_INDUCTIVE_SAME_NAME
