(** Regex derivatives
 *
 * Translation of Coq source to F*.
 * See Coq sources for a heavily commented version.
 *
 * Adapted from Coq source with help from Santiago Zanella-Beguelin
 *)
module RegularExpressions

open FStar.Squash
open FStar.Classical
open FStar.List.Tot

let op_Plus_Plus = FStar.List.Tot.Base.append

(** The alphabet for strings *)
assume val sigma: t:Type0{hasEq t}

type string : Type0 = list sigma

(** A language is traditionally a set of strings. In F*'s logic, the best way to
  express (possibly infinite) sets is as a predicate over strings; the
  interpretation will be that [forall (l:language) (s:string). l s] holds for exactly
  those strings in the language [l]. *)
type language = string -> GTot Type0

let is_in (s:string) (l:language) = l s

type regex =
  | Empty: regex (* Empty is the empty language, matching no strings. *)
  | Char : c:sigma -> regex
  | Or   : r1:regex -> r2:regex -> regex
  | Seq  : r1:regex -> r2:regex -> regex
  | Star : r:regex -> regex

(** eps is a derived regex that matches only the empty string. *)
let eps = Star Empty

noeq type star (l:language) : language =
  | Star_empty : star l []
  | Star_iter  : s1:string -> s2:string -> s1 `is_in` l -> star l s2 -> star l (s1 ++ s2)

(** The denotation of a regex is a language. These are the trusted semantics of
the regex type above. *)
val denotation: regex -> language
let rec denotation = function
  | Empty     -> fun s -> False
  | Char c    -> fun s -> s == [c]
  | Or r1 r2  -> fun s -> denotation r1 s \/ denotation r2 s
  | Seq r1 r2 -> fun s -> exists s1 s2. s == s1 ++ s2 /\ denotation r1 s1 /\ denotation r2 s2
  | Star r    -> fun s -> star (denotation r) s

(** Only the empty string is in the Kleene star of the empty language *)
val star_false: s:string -> star (fun _ -> False) s -> Lemma (s == [])
let star_false s = function
  | Star_empty -> ()
  | Star_iter s1 _ _ _ -> ()

val eps_denotation0: denotation eps []
let eps_denotation0 =
  Star_empty #(fun _ -> False)

val eps_denotation1: unit -> Lemma (denotation eps [])
let eps_denotation1 _ =
  give_witness (Star_empty #(fun _ -> False))

(* `eps` indeed represents the language consisting only of the empty string. *)
val eps_denotation: s:string -> Lemma (denotation eps s <==> s == [])
let eps_denotation s =
  eps_denotation1 ();
  impl_intro (star_false s)

(* The `observation_map` of a regex is one (equivalent to) `eps` if `[]`
  is in the language and one (equivalent to) `Empty` otherwise. *)
val observation_map: regex -> regex
let rec observation_map = function
  | Empty     -> Empty
  | Char _    -> Empty
  | Or r1 r2  -> Or (observation_map r1) (observation_map r2)
  | Seq r1 r2 -> Seq (observation_map r1) (observation_map r2)
  | Star r    -> eps

(* Characterization of observation_map: when the resulting regex holds,
  it is equivalent to `eps` (an artifact of how `observation_map` is defined)
  and `[]` is in `r` *)

val app_eq_nil1: s1:string -> s2:string -> s1 ++ s2 == [] -> Lemma (s1 == [])
let app_eq_nil1 s1 s2 _ = ()

val app_eq_nil2: s1:string -> s2:string -> s1 ++ s2 == [] -> Lemma (s2 == [])
let app_eq_nil2 s1 s2 _ = ()

let forall2_to_exists (#a:Type) (#b:Type) (#p:(a -> b -> Type)) (#r:Type)
  ($f:(x:a -> y:b -> Lemma (p x y ==> r))) : Lemma ((exists (x:a) (y:b). p x y) ==> r)
  = forall_intro_2 f

val observation_map1: r:regex -> s:string -> Lemma
  (denotation (observation_map r) s ==> s == [])
let rec observation_map1 r s =
  match r with
  | Empty     -> ()
  | Char _    -> ()
  | Or r1 r2  -> observation_map1 r1 s; observation_map1 r2 s
  | Seq r1 r2 ->
    let f (s1:string) (s2:string) : Lemma (s == s1 ++ s2 /\
                      denotation (observation_map r1) s1 /\
                      denotation (observation_map r2) s2 ==>
                      s == []) =
      observation_map1 r1 s1;
      observation_map1 r2 s2 in
     forall2_to_exists f;
     admit()
  | Star _  -> eps_denotation s

(** For any regex `r`, the language of `Star r` includes `[]` *)
val star_denotation: r:regex -> Lemma (denotation (Star r) [])
let star_denotation r =
  give_witness (Star_empty #(denotation r))

val observation_map2: r:regex -> Lemma
  (denotation (observation_map r) [] ==> denotation r [])
let rec observation_map2 = function
  | Empty     -> ()
  | Char _    -> ()
  | Or r1 r2  -> observation_map2 r1; observation_map2 r2
  | Seq r1 r2 -> admit()
  | Star r    -> star_denotation r

val observation_map_eps: r:regex -> s:string -> Lemma
  (denotation (observation_map r) s ==> s == [] /\ denotation r [])
let observation_map_eps r s =
  observation_map1 r s;
  observation_map2 r

val observation_map_holds: r:regex -> Lemma
  (denotation r [] ==> denotation (observation_map r) [])
let rec observation_map_holds = function
  | Empty     -> ()
  | Char _    -> ()
  | Or r1 r2  -> observation_map_holds r1; observation_map_holds r2
  | Seq r1 r2 -> admit()
  | Star r    -> observation_map2 r

(** Finally, we define the syntactic continuation map or derivative
    of a regular expression, with respect to `c`. *)
val continuation_map: sigma -> regex -> regex
let rec continuation_map c = function
  | Empty     -> Empty
  | Char c'   -> if c = c' then eps else Empty
  | Or r1 r2  -> Or (continuation_map c r1) (continuation_map c r2)
  | Seq r1 r2 -> Or
                  (Seq (continuation_map c r1) r2)
                  (Seq (observation_map r1) (continuation_map c r2))
  | Star r -> Seq (continuation_map c r) (Star r)

(** To write the correctness of the `continuation_map`, `derivative`
    defines the derivative for a language in a straightforward,
    interpretable way. *)
let derivative (c:sigma) (l:language) : language =
  fun s -> l (c :: s)

(** The correctness theorem has the form that two languages (the denotation
 *  of the continuation map and the derivative of the regex language) are the
 *  same.
 *  In F* the natural way to express that `l1` and `l2` are the same is to prove
 *  `forall s. l1 s <==> l2 s`. This is easiest done by proving each direction
 *  separately, amounting to proving `l1` is a subset of `l2` (`forall s. l1 s ==> l2 s`)
 *  and that `l2` is a subset of `l1` (`forall s. l2 s ==> l1 s`).
 *)

val continuation_map_denotes_derivative1: r:regex -> c:sigma -> s:string ->
  Lemma (denotation (continuation_map c r) s ==> derivative c (denotation r) s)
let rec continuation_map_denotes_derivative1 r c s =
  match r with
  | Empty     -> ()
  | Char _    -> eps_denotation s
  | Or r1 r2  -> continuation_map_denotes_derivative1 r1 c s;
                continuation_map_denotes_derivative1 r2 c s
  | Seq r1 r2 -> admit()
  | Star r'   -> admit()

val continuation_map_denotes_derivative2: r:regex -> c:sigma -> s:string ->
  Lemma (derivative c (denotation r) s ==> denotation (continuation_map c r) s)
let rec continuation_map_denotes_derivative2 r c s =
  match r with
  | Empty     -> ()
  | Char _    -> eps_denotation s
  | Or r1 r2  -> continuation_map_denotes_derivative2 r1 c s;
                continuation_map_denotes_derivative2 r2 c s
  | Seq r1 r2 -> admit()
  | Star r'   -> admit()

val continuation_map_denotes_derivative: r:regex -> c:sigma -> s:string ->
  Lemma (derivative c (denotation r) s <==> denotation (continuation_map c r) s)
let continuation_map_denotes_derivative r c s =
  continuation_map_denotes_derivative1 r c s;
  continuation_map_denotes_derivative2 r c s

(** * With these definitions it is easy to write a regex matcher, verified
  against the denotation given above *)

(** auxiliary function to make `observation_map` computable *)
val includes_nil: r:regex -> b:bool{
  (b ==> denotation (observation_map r) []) /\
  (~b ==> (forall s. ~(denotation (observation_map r) s))) }
let rec includes_nil = function
  | Empty     -> false
  | Char _    -> false
  | Or r1 r2  -> includes_nil r1 || includes_nil r2
  | Seq r1 r2 -> (admit(); includes_nil r1 && includes_nil r2)
  | Star r    -> true

(** Regex matching, with correctness built into the return type *)
val regex_match: r:regex -> s:string -> Tot (b:bool{b <==> denotation r s}) (decreases s)
let rec regex_match r s =
  match s with
  | [] ->
    observation_map_holds r;
    observation_map_eps r s;
    includes_nil r
  | c::s0 ->
    continuation_map_denotes_derivative r c s0;
    regex_match (continuation_map c r) s0
