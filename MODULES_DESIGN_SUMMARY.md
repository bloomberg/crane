# Rocq Modules to C++ Template Structs: Design Summary

## High-Level Transformation

```
Rocq Syntax                    →  C++ Output
─────────────────────────────────────────────────────────

Module Type:                     Concept with requires clauses
  module type Sig = sig            template<typename M>
    type Key                        concept Sig = requires {
    val find : Key → Value            typename M::Key;
  end                                 M::find(...) -> ...
                                    };

Regular Module:                  Struct
  module M = struct              struct M {
    let x = 5                      static inline int x = 5;
  end                            };

Functor:                         Template struct
  module Map(K: Ord) = struct    template<OrderedType K>
    type t = K.t × int          struct Map {
    let get = ...                  using t = typename K::t;
  end                              static auto get(...) { ... }
                                 };

Functor Application:             Template instantiation
  module IntMap = Map(Int)       using IntMap = Map<int>;

Inductive in Module:             Nested struct
  module Bst = struct            struct Bst {
    type tree = Node | Leaf        struct tree { ... };
  end                            };
```

## Key Design Principles

### 1. Module Types → C++ Concepts

Module types define an interface. Rather than duck typing, we use C++ concepts
to explicitly encode the requirements:

**Rocq:**
```ocaml
module type ORDERED = sig
  type t
  val compare : t → t → bool
end
```

**C++:**
```cpp
template<typename M>
concept ORDERED = requires {
  typename M::t;
  { M::compare(std::declval<M::t>(), std::declval<M::t>()) } -> std::same_as<bool>;
};
```

### 2. Modules → Template Structs

Modules become structs that can have template parameters:

**Rocq:**
```ocaml
module BSTMap(K: ORDERED) = struct
  type key = K.t
  let find = ...
end
```

**C++:**
```cpp
template<ORDERED K>
struct BSTMap {
  using key = typename K::t;
  static auto find(...) { ... }
};
```

### 3. Type Parameters → Concepts

When a module is a functor parameter, its type is a concept:

**Rocq:**
```ocaml
module Make(Key: ORDERED)(Val: BASE) = struct ... end
```

**C++:**
```cpp
template<ORDERED Key, BASE Val>
struct Make {
  // ...
};
```

### 4. Functor Applications → Template Instantiation

Applying a functor to arguments becomes a template instantiation:

**Rocq:**
```ocaml
module IntBST = BSTMap(Int)
```

**C++:**
```cpp
using IntBST = BSTMap<int>;
```

## Implementation Details

### Context Tracking

A mutable `in_struct_context` ref tracks whether we're inside a module struct:

```ocaml
let in_struct_context = ref false
```

**Why this is needed:**
1. Functions inside structs need `static` keyword (no implicit this)
2. Nested inductives become nested structs (not namespaces)
3. Variable initializers need `static inline` (C++17)

**Usage:**
- Set to `true` when entering a named namespace (converted to struct)
- Functions check it to add `static` keyword
- Inductives check it to decide on wrapping

### Namespace → Struct Transformation

Namespaces representing inductive types become structs:

```ocaml
| Dnspace (Some id, decls) ->
    let old_context = !in_struct_context in
    in_struct_context := true;
    let ds = pp_list_stmt (pp_cpp_decl env) decls in
    in_struct_context := old_context;
    let struct_name = match id with
      | GlobRef.IndRef (kn, i) ->
          str (String.capitalize_ascii (str_global Type id))
      | _ -> pp_global Type id
    in
    h (str "struct " ++ struct_name ++ str " {" ++ fnl () ++ ds ++ fnl () ++ str "};")
```

**Why capitalize:**
- Inductive `list` lives in struct `List` (capitalized)
- Avoids name conflicts
- Follows C++ naming conventions

### Local vs Non-local Inductives

Inductives are tracked in a context list:

```ocaml
let local_inductives : GlobRef.t list ref = ref []
```

**Behavior:**
- **Local inductives:** No `Tnamespace` wrapper, direct reference
- **Non-local inductives:** Qualified with namespace struct prefix (e.g., `List::list`)

**Example:**
```cpp
// In module MakeMap<K, V>:
struct tree {
  struct Node;        // local - no prefix
};

// At module scope:
struct Tree {         // wrapper struct for namespace
  struct tree { ... }; // the actual type
};
```

### Static Keywords for Struct Members

Functions inside structs need `static`:

```ocaml
let is_qualified = List.length ids > 1 || (match ids with
  | [(_, tys)] when tys <> [] -> true | _ -> false) in
let is_struct_member = is_qualified || !in_struct_context in
let static_kw = if is_struct_member then str "static " else mt () in
```

**Heuristics:**
1. Qualified names like `Module::func` → member function
2. Template functions `Module::func<T>` → member function
3. Inside `in_struct_context` → definitely a member

### Static Inline for Constants

C++17 allows `static inline` in struct definitions:

```cpp
template<OrderedType K>
struct Map {
  static inline int max_size = 1000;  // No linker errors!
};
```

**Why needed:**
- Without `inline`, multiple includes cause duplicate symbol errors
- `inline` allows the definition to appear multiple times
- Compiler can use the definition for optimizations

### Template-Dependent Types

Accessing nested types from template parameters requires `typename`:

```cpp
template<typename M>
struct UseM {
  using key = typename M::Key;  // Need typename!
};
```

**Generated by `Tqualified`:**
```ocaml
| Tqualified (base_ty, nested_id) ->
    str "typename " ++ base_str ++ str "::" ++ Id.print nested_id
```

### Mutual Recursion Support

Mutual inductives need forward declarations:

```cpp
struct A;         // forward declaration
struct B;         // forward declaration

struct A {
  B b;            // now B is known
};

struct B {
  A a;            // now A is known
};
```

**Generated in `pp_cpp_ind_header`:**
```ocaml
let is_mutual = Array.length ind.ind_packets > 1 in
let forward_decls =
  if is_mutual then
    (* generate: struct A; struct B; *)
```

## Generated Code Examples

### Example 1: Simple Module

**Rocq:**
```rocq
Module M.
  Definition x := 42.
End M.
```

**C++:**
```cpp
struct M {
  static inline int x = 42;
};
```

### Example 2: Functor with Concepts

**Rocq:**
```rocq
Module Type ELEMENT := sig
  Definition t : Type
End ELEMENT.

Module MakeList(E : ELEMENT) := struct
  Definition head : E.t → list E.t → list E.t := ...
End MakeList.

Module IntList := MakeList(int).
```

**C++:**
```cpp
template<typename M>
concept ELEMENT = requires {
  typename M::t;
};

template<ELEMENT E>
struct MakeList {
  using element = typename E::t;
  static auto head(element, std::shared_ptr<list<element>>)
    -> std::shared_ptr<list<element>> { ... }
};

using IntList = MakeList<int>;
```

### Example 3: Nested Inductives

**Rocq:**
```rocq
Module BinaryTree := struct
  Inductive tree :=
  | Leaf : tree
  | Node : tree → tree → tree
End BinaryTree.
```

**C++:**
```cpp
struct BinaryTree {
  struct tree {
    struct ctor {
      static auto Leaf_() { ... }
      static auto Node_(std::shared_ptr<tree>, std::shared_ptr<tree>) { ... }
    };

    std::variant<...> v_;
  };
};
```

## Known Limitations

1. **Nested modules:** Not yet supported in concepts
2. **Inductive requirements:** Can't express inductive types in concept requirements
3. **With type constraints:** Module type refinements not fully supported
4. **Higher-order functors:** Functors taking functors as arguments need investigation

## Benefits of This Design

1. **Type Safety:** Concepts provide compile-time checking of module compatibility
2. **Zero Overhead:** Templates compile to efficient machine code
3. **Cleaner Syntax:** Modules feel natural in C++ as structs/templates
4. **Good Error Messages:** C++ concepts provide clear error reporting
5. **Optimizer Friendly:** All information available at instantiation time

## Future Improvements

1. Support nested module types in concepts
2. Add inductive type representations to concept requirements
3. Implement module refinement (with type/module constraints)
4. Support functors taking functor parameters
5. Generate better error messages for concept violations
