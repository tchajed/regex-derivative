(**
 * Extract an executable OCaml implementation from the Coq regex matcher.
*)
Require Import Extraction.
Require Import regex.
Require Import Ascii.

(** Recall that we wrote the regex matcher for an arbitrary alphabet Sigma -
here we extract methods specialized to lists of characters. *)

Definition matcher := lazy_regex_match ascii Ascii.ascii_dec.

Extraction Language OCaml.

(** These directives cause the ascii datatype in Coq (which is just 8 booleans)
to be extracted to a native char. Taken from Software Foundations Imp
extraction. *)

Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) → let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) (fun f c → let n = Char.code c in let h i = (n land (1 lsl i)) ≠ 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant zero => "'\000'".
Extract Constant one => "'\001'".
Extract Constant shift =>
 "fun b c → Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec => "(=)".

(** We also replace Coq's sumbool (which carries proofs) and bool (which need
not be defined inductively) with regular OCaml booleans *)
Extract Inductive sumbool => "bool" ["true" "false"].
Extract Inductive bool => "bool" ["true" "false"].

(** Extract matcher, with its dependencies. to the file "regex.ml". *)
Extraction "regex.ml" matcher.
