From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Crane Require Extraction.

(**
  Bug: a Rocq name that is also a global C library name is not escaped.

  [Definition select := nat] becomes [using select = uint64_t;] at global
  scope. glibc declares the function [::select] in <sys/select.h>, which
  <iostream> pulls in, so a program including both does not compile:
  "redefinition of 'select' as different kind of symbol".

  Crane already escapes [uint64_t], [size_t] and similar library names
  (Cpp_state.keywords); POSIX functions such as [select] are not covered.
*)

Definition select := nat.

Definition answer : select := 42.

Crane Extraction "select_type_alias_clash" answer.
