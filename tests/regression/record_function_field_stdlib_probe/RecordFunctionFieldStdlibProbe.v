From Crane Require Extraction.

Module RecordFunctionFieldStdlibProbe.

Record endo : Type := {
  run : bool -> bool
}.

Definition e : endo := {| run := negb |}.

Definition sample : bool := run e true.

End RecordFunctionFieldStdlibProbe.

Crane Extraction "record_function_field_stdlib_probe" RecordFunctionFieldStdlibProbe.
