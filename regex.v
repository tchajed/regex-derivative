(** Regex derivatives
 *
 * Regular expression derivatives are a particularly elegant approach
 * to matching and reasoning about regular expressions and
 * languages. The idea is to consider the derivative of a language L
 * (a set of strings) with respect to a character c, defined as {w |
 * cw in L}. In terms of automata, what does the automata match if fed
 * a c first? It happens that the derivative of a regular expression
 * can be defined purely syntatically.
 *
 * This development defines regexes as syntax and as predicates,
 * defines derivatives syntactically and as a transformation of a
 * predicate, and proves a relationship between these
 * two. Specifically, [[ dr/dc ]] = d [[ r ]]/dc, abusing d/dc for
 * both the syntatic and denotational derivative and using [[ r ]] to
 * denote the denotation of a regex.
 *)

Require Import List.

(** A bit of automation to instantiate existential hypotheses *)
Ltac deex :=
  match goal with
  | [ H: exists (varname: _), _ |- _ ] =>
    let name := fresh varname in
    destruct H as [name ?];
    repeat match goal with
           | [ H: _ /\ _ |- _ ] =>
             destruct H
           end
  end.

Section RegularExpressions.

  (** The alphabet for strings *)
  Variable Sigma:Type.
  (** We only require decidable equality on the alphabet for matching
  and derivatives to work (in particular, no finiteness
  constraint). *)
  Variable Sigma_dec : forall (c c': Sigma), {c = c'} + {c <> c'}.

  Definition string_dec : forall (s s': list Sigma), {s = s'} + {s <> s'} :=
    List.list_eq_dec Sigma_dec.

  Inductive regex :=
    (** Empty is the empty language, matching no strings. *)
  | Empty
  | Char (s:Sigma)
  | Or (r1:regex) (r2:regex)
  | Seq (r1:regex) (r2:regex)
  | Star (r:regex).

  (** Eps is a derived regex that matches only the empty string. *)
  Definition Eps := Star Empty.

  (** First we give an auxiliary inductive definition for the
  denotation of Kleene star of an arbitrary proposition. *)
  Inductive star (P: list Sigma -> Prop) : list Sigma -> Prop :=
  | star_empty : star P nil
  | star_iter : forall s1 s2,
      P s1 ->
      star P s2 ->
      star P (s1 ++ s2).

  (** The denotation of a regex is a language, expressed as a
  predicate over strings. *)
  Fixpoint denotation (r:regex) : list Sigma -> Prop :=
    match r with
    | Empty => fun _ => False
    | Char s => fun l => l = s::nil
    | Or r1 r2 => fun l => denotation r1 l \/ denotation r2 l
    | Seq r1 r2 => fun l =>
                    exists l1 l2, l = l1 ++ l2 /\
                             denotation r1 l1 /\
                             denotation r2 l2
    | Star r => fun l => star (denotation r) l
    end.

  (* We will want to automatically prove the denotation star with its
  constructors *)
  Hint Constructors star.

  Lemma star_false : forall l,
      star (fun _ => False) l ->
      l = nil.
  Proof.
    inversion 1; intuition.
  Qed.

  Ltac crush :=
    repeat match goal with
           | _ => progress (intros; simpl in *; subst)
           | _ => deex
           | [ H: nil = _ ++ _ |- _ ] =>
             destruct (app_eq_nil _ _ (eq_sym H))
           | [ H: star (fun _ => False) _ |- _ ] =>
             apply star_false in H
           | [ H: _ :: _ = _ :: _ |- _ ] =>
             inversion H; clear H
           | _ => progress (intuition eauto 10)
           | _ => congruence
           end.

  (* Eps indeed represents the language consisting only of the empty string. *)
  Remark eps_denotation : forall l, denotation Eps l <-> l = nil.
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

    Lemma observation_map_1 : forall r l,
      denotation (observation_map r) l ->
      l = nil.
    Proof.
      induction r; crush.
      rewrite (IHr1 l1); eauto.
    Qed.

    Lemma observation_map_2 : forall r,
        denotation (observation_map r) nil ->
        denotation r nil.
    Proof.
      induction r; crush.
      exists nil, nil; intuition.
    Qed.

    Lemma observation_map_eps : forall r l,
        denotation (observation_map r) l ->
        (l = nil /\ denotation r nil).
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
      exists nil, nil; intuition eauto.
    Qed.

  End ObservationMap.

  (** Finally, we define the syntactic continuation map or derivative
    of a regular expression, with respect to c. *)
  Section Derivative.
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
  Definition derivative (c:Sigma) (P: list Sigma -> Prop) : list Sigma -> Prop :=
    fun l => P (c :: l).

  Hint Resolve app_comm_cons.
  Hint Resolve observation_map_eps observation_map_holds.

  Theorem continuation_map_denotes_derivative_1 : forall r c,
      forall l, denotation (continuation_map c r) l ->
           derivative c (denotation r) l.
  Proof.
    unfold derivative.
    induction r; crush.
    - destruct (Sigma_dec c s); crush.
    - pose proof (observation_map_eps _ _ H0); crush.
      exists nil.
      eexists; crush.
    - rewrite app_comm_cons.
      eauto.
  Qed.

  Theorem continuation_map_denotes_derivative_2 : forall r c,
      forall l, derivative c (denotation r) l ->
           denotation (continuation_map c r) l.
  Proof.
    unfold derivative.
    induction r; crush.
    - destruct (Sigma_dec s s); crush.
    - destruct l1; [ right | left ]; crush.
      exists nil, l; crush.
    - remember (c::l).
      generalize dependent l.
      match goal with
      | [ H: star _ _ |- _ ] => induction H; crush
      end.
      destruct s1; crush.
  Qed.

  Theorem continuation_map_denotes_derivative : forall r c,
      forall l, denotation (continuation_map c r) l <->
           derivative c (denotation r) l.
  Proof.
    split; auto using continuation_map_denotes_derivative_1,
           continuation_map_denotes_derivative_2.
  Qed.

  Section Matching.

    (** auxilliary function to make observation_map computable *)
    Definition includes_nil r : {denotation (observation_map r) nil} + {forall l, ~denotation (observation_map r) l}.
      induction r; crush; try solve [ left + right; crush ].
      left; exists nil, nil; crush.
    Defined.

    Hint Resolve observation_map_2.

    (** Regex matching, with correctness built into the return type *)
    Fixpoint regex_match r s : {denotation r s} + {~denotation r s}.
      destruct s.
      - destruct (includes_nil r); solve [ left + right; crush ].
      - destruct (regex_match (continuation_map s r) s0).
        left; apply continuation_map_denotes_derivative_1 in d; eauto.
        right; eauto using continuation_map_denotes_derivative_2.
    Defined.

  End Matching.

End RegularExpressions.