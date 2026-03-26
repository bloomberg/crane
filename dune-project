(lang dune 3.13)
(name rocq-crane)

(using coq 0.8)

(formatting
 (enabled_for ocaml))

(package
 (name rocq-crane)
 (depends
   (ocaml (>= 4.14.0))
   (coq (>= "9.0~"))
   (rocq-core (>= "9.0~"))
   (rocq-stdlib (>= "9.0~"))
   (coq-ext-lib (>= "0.13.0"))
   (ocaml-lsp-server :with-dev-setup)))
