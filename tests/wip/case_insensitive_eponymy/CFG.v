(** Crane bug: a file whose name matches a type it declares only up to case
    takes the name, and the type is emitted with no name at all.

    [CFG.v] declares the record [cfg].  Crane emits

      template <typename T> struct {
        block_id init;
        ocfg<T> blks;
      };

    -- a class template with no name -- and every use of [cfg] then has
    nothing to refer to.  Nothing is reported at extraction time.

    The exact-match case is handled: rename the record to [CFG] and the module
    gives way, as d77449c8 made it do.  Only the case-insensitive match
    still loses.

    Expected: one of the two is renamed, as for an exact match.
    Actual:   error: cannot declare a class template with no name
              error: declaration does not declare anything
              error: unknown type name 'cfg'

    Seen in Vellvm on [Syntax/CFG.v] against the record [cfg] in it; it used to
    be worked around with [Crane Extraction Blacklist CFG]. *)

From Crane Require Extraction.
From Stdlib Require Import List.

Record cfg (T : Type) : Type := mk_cfg { init : nat ; blks : list T }.
Arguments mk_cfg {T}.
Arguments blks {T}.

Definition size {T : Type} (g : cfg T) : nat := length (blks g).
