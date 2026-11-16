(lang dune 3.13)
(name rocq-crane)

(using coq 0.8)

(formatting
 (enabled_for ocaml))

(package
 (name rocq-crane)
 (depends
   (ocaml (>= 4.14.0))
   (coq (and (>= "9.1~") (< "9.2~")))
   (rocq-core (and (>= "9.1~") (< "9.2~")))
   (rocq-stdlib (>= "9.0~"))
   (coq-ext-lib (>= "0.13.0"))
   (coq-color (>= "1.8.0"))
   (ocaml-lsp-server :with-dev-setup)))
