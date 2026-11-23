Explore common topics, guides, and documentation for Crane.

| | |
|---|---|
| **[Getting Started](Getting-Started.md)**<br>Install Crane, configure Rocq, and run your first extraction. | **[Design Principles](Design-Principles.md)**<br>The goals and tradeoffs behind Crane's C++ extraction strategy. |
| **[Examples](Examples.md)**<br>Browse example Rocq projects and extracted C++ code. | **[Reference Manual](Reference-Manual.md)**<br>Every Crane command, option, mapping form and flag. |
| **[Crane Base Library](Crane-Base-Library.md)**<br>Mappings, effects, and the C++ runtime used by extracted code. | **[Roadmap](Roadmap.md)**<br>What recently landed and what comes next. |

## Design and internals

- [Compiler Pipeline](Compiler-Pipeline.md): the stages, intermediate
  languages, finishing passes, checks and developer switches of the plugin.
- [Crane Bake](Crane-Bake.md): computing constants at extraction time and
  extracting them as data; the image format and stale-image detection.
- [Typed Mappings Design](typed-mappings-design.md): the model behind
  `TypeMapping` and `OperationMapping` (copy, access, views, lifetimes,
  operation contracts).
- [Typed CppIR Design](typed-cppir-design.md): typed lowering, slot types and
  the single coercion decision, with the findings of each phase.
