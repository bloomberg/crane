# Module Implementation Log

## Goal
Implement Rocq modules in Crane using C++ concepts and template structs, following the pattern:
- Module types → C++ concepts
- Modules → C++ structs
- Functors → C++ template structs
- Module applications → Template instantiations

## Changes Made

### 1. Initial exploration (completed)
- Examined existing module handling in cpp.ml
- Current implementation uses OCaml-style `functor` keyword (not valid C++)
- Module types were partially implemented as concepts
- Modules were implemented as namespaces

### 2. Implementation of module types as concepts (completed)
**File: src/cpp.ml**

- Added `pp_spec_as_requirement` function to convert specifications to C++ requires clauses
- Modified `pp_module_type` to generate concept bodies instead of OCaml-style signatures
  - `MTident kn` → just the concept name reference
  - `MTfunsig` → returns the body type (template params handled in functor generation)
  - `MTsig` → generates requires clauses from specifications
- Updated `SEmodtype` in `pp_structure_elem` to generate proper C++ concepts with template parameters:
  ```cpp
  template<typename M>
  concept ConceptName = requires {
    typename M::member;
    ...
  };
  ```

### 3. Implementation of modules as structs (completed)
**File: src/cpp.ml**

- Modified `pp_structure_elem` for `SEmodule` to generate structs instead of namespaces:
  - Regular modules → `struct Name { ... };`
  - Module applications → `using Name = Base<Args>;`
  - Functors → handled separately with template parameters

### 4. Implementation of functors as template structs (completed)
**File: src/cpp.ml**

- Modified `pp_module_expr` to handle functor applications properly
- Updated `MEapply` to collect all arguments and generate single template instantiation:
  - `MakeMap ZOrdered ZBase` → `MakeMap<ZOrdered, ZBase>` (not `MakeMap<ZOrdered><ZBase>`)
- Implemented template struct generation for functors in `pp_structure_elem`:
  ```cpp
  template<ConceptName1 Param1, ConceptName2 Param2>
  struct FunctorName {
    ...
  };
  ```

### 5. Extraction results
Successfully extracted the module test (Module.v) to C++ code with:
- ✅ Module types generated as C++ concepts with template parameters
- ✅ Modules generated as C++ structs
- ✅ Functors generated as template structs with concept constraints
- ✅ Module applications generated as template instantiations

### 6. Debug improvements
**File: src/extract_env.ml**
- Modified extraction error reporting to always show full exception messages and backtraces

## Known Issues

### 1. Inductives inside modules generate invalid C++ (HIGH PRIORITY)
**Problem:** Inductives are always generated as namespaces (via `Dnspace` in translation.ml:352). When an inductive is defined inside a module (which becomes a struct), we get invalid C++ like:
```cpp
template<OrderedType K, BaseType V> struct MakeMap {
  using key = K::t;
  using value = V::t;

  namespace tree {  // ❌ INVALID: namespace inside struct
    struct Empty { ... };
    struct Node { ... };
    ...
  };
};
```

**Expected:** Inductives inside modules should be generated as nested structs:
```cpp
template<OrderedType K, BaseType V> struct MakeMap {
  using key = typename K::t;
  using value = typename V::t;

private:
  struct Tree {
    struct Node;
    using Ptr = std::shared_ptr<const Node>;
    ...
  };

public:
  using t = Tree;
  ...
};
```

**Solution needed:**
- Modify `gen_ind_cpp` in translation.ml to accept context about whether it's inside a module
- Generate `Dstruct` instead of `Dnspace` when inside a module
- Alternatively, add a post-processing pass to transform namespaces to structs when inside modules

**Files to modify:**
- `src/translation.ml` - gen_ind_cpp function (line 340-352)
- Possibly `src/cpp.ml` - pp_cpp_ind function to pass context

### 2. Missing `typename` keywords
Some type references need `typename` keyword for dependent types (e.g., `using key = typename K::t;`)

### 3. Name conflicts
The Z inductive namespace and Z module struct have the same name, causing conflicts.

## Testing
- Extraction succeeds: `tests/basics/mymap/mymap.{h,cpp}` generated
- C++ compilation fails due to namespace-inside-struct issue
- Once inductive generation is fixed, the code should compile and run

## Files Modified
1. `src/cpp.ml` - Module generation logic
2. `src/extract_env.ml` - Error reporting
3. `CLAUDE.md` - This log file
