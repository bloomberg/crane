Class Params : Type := { ptr : Type ; zero : ptr }.
Class MemState {Pa : Params} : Type := { state : Type ; initial_state : state ; size_of : state -> nat }.
Definition memM {Pa : Params} {MS : @MemState Pa} (A : Type) : Type := state -> (state * A).
