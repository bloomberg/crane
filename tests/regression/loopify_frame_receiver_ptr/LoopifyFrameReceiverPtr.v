(** A loopified function methodified onto [String].  The resume frame declares
    the saved receiver as a pointer but the value pushed into it is an object:

    {v
      no viable conversion from 'const String' to 'const String *'
      member reference type 'const String *' is a pointer; did you mean to use '->'?
    v} *)

From Crane.Mapping Require Import Std.
Require Import String List.

Module LoopifyFrameReceiverPtr.

Definition f (l : list string) : string := String.concat ","%string l.

End LoopifyFrameReceiverPtr.

Crane Extraction "loopify_frame_receiver_ptr" LoopifyFrameReceiverPtr.
