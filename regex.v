(** Regex derivatives
 *
 * Regular expression derivatives are a particularly elegant approach
 * to matching and reasoning about regular expressions and
 * languages. The idea is to consider the derivative of a language L
 * (a set of strings) with respect to a character c, defined as {w |
 * cw in L}. In terms of automata, what does the automata match if fed the
 * character c first? It turns out that derivatives of regular languages have
 * two nice properties: the derivative of a regular language is regular, and the
 * derivative of a language expressed as a regular expression can be expressed
 * in a simple syntatic manner.
 *
 * This development defines regexes as syntax and as predicates,
 * defines derivatives syntactically and as a transformation of a
 * predicate, and proves a relationship between these
 * two. Specifically, [[ dr/dc ]] = d [[ r ]]/dc, abusing d/dc for
 * both the syntatic and denotational derivative and using [[ r ]] to
 * denote the denotation of a regex.
 *
 * These derivative tools give a simple and natural regex matcher with a
 * correctness proof in its type.
 *)

Require Import List.

Section RegularExpressions.

  (** The alphabet for strings *)
  Variable Sigma:Type.
  (** We only require decidable equality on the alphabet for matching
  and derivatives to work (in particular, no finiteness
  constraint). *)
  Variable Sigma_dec : forall (c c': Sigma), {c = c'} + {c <> c'}.

  (** * Standard names

  These simple definitions give standard names from the theory of computation to
  the analogues in this setting.
   *)

  (** A string takes elements from the (arbitrary) alphabet above. *)
  Definition string := list Sigma.
  (** A language is traditionally a set of strings. In Coq's constructive logic,
  the best to express (possibly infinite) sets is as a predicate over strings;
  the interpretation will be that forall (l: language) (s: string), l s is true
  for exactly those strings in the language l *)
  Definition language := string -> Prop.

  (** A cool feature of Coq, mirroring standard practice in programming languages papers.

  This command means, for example, that when we use the letter s for a variable
  without a type annotation, it should default to being of type string, before
  types are inferred.

   This might seem like a horrible thing to do, and it is indeed confusing when
   done on a whiteboard or in a paper, but here it serves an important purpose:
   it ensures that when we use the letters c, s, or l (or those characters
   followed by numbers or prime symbols ' actually), they must represent the
   expected type. *)
  Implicit Types (c: Sigma) (s: string) (l: language).

  Definition string_dec : forall (s s': string), {s = s'} + {s <> s'} :=
    List.list_eq_dec Sigma_dec.

  Inductive regex :=
    (** Empty is the empty language, matching no strings. *)
  | Empty
  | Char (c:Sigma)
  | Or (r1:regex) (r2:regex)
  | Seq (r1:regex) (r2:regex)
  | Star (r:regex).

  (** Eps is a derived regex that matches only the empty string. *)
  Definition Eps := Star Empty.

  (** First we give an auxiliary inductive definition to take the Kleene star of
  a language. *)
  Inductive star (l: language) : language :=
  | star_empty : star l nil
  | star_iter : forall s1 s2,
      l s1 ->
      star l s2 ->
      star l (s1 ++ s2).

  (** The denotation of a regex is a language.

      Regular expressions give a nice way to think about denotational vs
      operational definitions. We could define what a regular expression does in
      terms of an automata, which gives regexes a meaning operationally.
      Instead, we give a denotation (think "interpretation" or "meaning") for
      each regex, mapping them to a concept we have in our metatheory.

      Normally the metatheory is mathematics, but here we are using the Coq
      programming language as the metatheory. In mathematics we would use a set
      of strings as the denotation of a regex, whereas here we use [language] as
      defined above. *)
  Fixpoint denotation (r:regex) : language :=
    match r with
    | Empty => fun _ => False
    | Char c => fun s => s = c::nil
    | Or r1 r2 => fun s => denotation r1 s \/ denotation r2 s
    | Seq r1 r2 => fun s =>
                    exists s1 s2, s = s1 ++ s2 /\
                             denotation r1 s1 /\
                             denotation r2 s2
    | Star r => fun s => star (denotation r) s
    end.

  (* We will want to automatically prove the denotation star with its
  constructors *)
  Hint Constructors star.

  Lemma star_false : forall s,
      star (fun _ => False) s ->
      s = nil.
  Proof.
    inversion 1; intuition.
  Qed.

  (** Some automation that covers most proofs here. *)

  (* Helper for instantiating existential hypotheses, preserving names. *)
  Ltac deex H :=
    lazymatch type of H with
    | exists (varname: _), _ =>
      let name := fresh varname in
      destruct H as [name ?]
    end.

  Ltac crush :=
    repeat match goal with
           | _ => progress (intros; simpl in *; subst)
           | [ H: exists _, _ |- _ ] => deex H
           | [ H: nil = _ ++ _ |- _ ] =>
             destruct (app_eq_nil _ _ (eq_sym H))
           | [ H: star (fun _ => False) _ |- _ ] =>
             apply star_false in H
           | [ H: _ :: _ = _ :: _ |- _ ] =>
             inversion H; clear H
           | _ => progress (intuition eauto 10)
           | [ |- exists (_ : string), _ ] =>
             solve [ exists nil; crush ]
           | _ => congruence
           end.

  (* Eps indeed represents the language consisting only of the empty string. *)
  Remark eps_denotation : forall s, denotation Eps s <-> s = nil.
  Proof.
    crush.
  Qed.

  (* The [observation_map] of a regex is one (equivalent to) Eps if nil
  is in the language and one (equivalent to) Empty otherwise. *)
  Fixpoint observation_map (r:regex) : regex :=
    match r with
    | Empty => Empty
    | Char _ => Empty
    | Or r1 r2 => Or (observation_map r1) (observation_map r2)
    | Seq r1 r2 => Seq (observation_map r1) (observation_map r2)
    | Star r => Eps
    end.

  (** Characterization of observation_map: when the resulting regex
  holds, it is equivalent to Eps (an artifact of how observation_map
  is defined) and nil is in r *)
  Section ObservationMap.

    Lemma observation_map_1 : forall r s,
      denotation (observation_map r) s ->
      s = nil.
    Proof.
      induction r; crush.
      rewrite (IHr1 s1); eauto.
    Qed.

    Lemma observation_map_2 : forall r,
        denotation (observation_map r) nil ->
        denotation r nil.
    Proof.
      induction r; crush.
    Qed.

    Lemma observation_map_eps : forall r s,
        denotation (observation_map r) s ->
        (s = nil /\ denotation r nil).
    Proof.
      intros.
      pose proof (observation_map_1 _ _ H); subst.
      intuition auto using observation_map_2.
    Qed.

    (* converse to the above *)
    Lemma observation_map_holds : forall r,
        denotation r nil ->
        denotation (observation_map r) nil.
    Proof.
      induction r; crush.
    Qed.

  End ObservationMap.

  (** Finally, we define the syntactic continuation map or derivative
    of a regular expression, with respect to c. *)
  Section Derivative.
    (** This is the character we are taking the derivative with respect to.
    Making it a variable means we don't have to pass it in recursive calls. *)
    Variable c:Sigma.

    Fixpoint continuation_map (r:regex) : regex :=
      match r with
      | Empty => Empty
      | Char c' => if Sigma_dec c c' then Eps else Empty
      | Or r1 r2 => Or (continuation_map r1) (continuation_map r2)
      | Seq r1 r2 => Or
                      (Seq (continuation_map r1) r2)
                      (Seq (observation_map r1) (continuation_map r2))
      | Star r => Seq (continuation_map r) (Star r)
      end.
  End Derivative.

  (** To write the correctness of the continuation_map, [derivative]
  defines derivative for a language in a straightforward,
  interpretable way. *)
  Definition derivative (c:Sigma) (l: language) : language :=
    fun s => l (c :: s).

  Hint Resolve app_comm_cons.
  Hint Resolve observation_map_eps observation_map_holds.

  (** The correctness theorem is that two languages are the same.

      In Coq the natural way to express that l1 and l2 are the same is to prove
      forall s, l1 <-> l2. This is easiest done by proving each direction
      separately, amounting to proving l1 is a subset of l2 (forall s, l1 -> l2)
      and that l2 is a subset of l1 (forall s, l2 -> l1). *)

  Theorem continuation_map_denotes_derivative_1 : forall r c,
      forall s, denotation (continuation_map c r) s ->
           derivative c (denotation r) s.
  Proof.
    unfold derivative.
    induction r; crush.
    - destruct (Sigma_dec c0 c); crush.
    - do 2 eexists; crush.
    - pose proof (observation_map_eps _ _ H); crush.
    - rewrite app_comm_cons.
      eauto.
  Qed.

  Theorem continuation_map_denotes_derivative_2 : forall r c,
      forall s, derivative c (denotation r) s ->
           denotation (continuation_map c r) s.
  Proof.
    unfold derivative.
    induction r; crush.
    - destruct (Sigma_dec c c); crush.
    - destruct s1; solve [ left + right; crush ].
    - remember (c::s).
      generalize dependent s.
      match goal with
      | [ H: star _ _ |- _ ] => induction H; crush
      end.
      destruct s1; crush.
  Qed.

  Theorem continuation_map_denotes_derivative : forall r c,
      forall s, denotation (continuation_map c r) s <->
           derivative c (denotation r) s.
  Proof.
    split; auto using continuation_map_denotes_derivative_1,
           continuation_map_denotes_derivative_2.
  Qed.

  (** With these definitions it is easy to write a regex matcher, verified
  against the denotation given above *)

  Section Matching.

    Ltac t := try solve [ left + right; crush ].

    (** auxilliary function to make observation_map computable *)
    Definition includes_nil r :
      {denotation (observation_map r) nil} +
      {forall s, ~denotation (observation_map r) s}.
      induction r; crush; t.
    Defined.

    (** unfold definition of derivative to drive hints *)
    Definition derivative_unfold : forall r c s,
        derivative c (denotation r) s ->
        denotation r (c::s)
      := ltac:(auto).

    Hint Resolve derivative_unfold.
    Hint Resolve observation_map_2.
    Hint Resolve continuation_map_denotes_derivative_1.
    Hint Resolve continuation_map_denotes_derivative_2.

    (** Regex matching, with correctness built into the return type *)
    Fixpoint regex_match r s : {denotation r s} + {~denotation r s}.
      destruct s.
      - destruct (includes_nil r); t.
      - destruct (regex_match (continuation_map s r) s0); t.
    Defined.

    Section LazyEvaluation.

      (** Check if a regex represents the empty language. *)
      Fixpoint is_empty r : {forall s, ~denotation r s} + {exists s, denotation r s}.
        destruct r; simpl; t.
        - destruct (is_empty r1); t.
          destruct (is_empty r2); t.
        - destruct (is_empty r1); t.
          destruct (is_empty r2); t.
      Defined.

      (** This (probably more efficient) matcher first checks if the regex
      language has become empty; if so, it stops matching and uses the is_empty
      proof underneath a right constructor *)
      Fixpoint lazy_regex_match r s : {denotation r s} + {~denotation r s}.
        destruct s.
        - destruct (includes_nil r); t.
        - destruct (is_empty (continuation_map s r)); t.
          destruct (regex_match (continuation_map s r) s0); t.
      Defined.

    End LazyEvaluation.

  End Matching.

End RegularExpressions.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ)) *)
(* End: *)
