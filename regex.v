Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section RegularExpressions.
  Variable Sigma:Type.
  Variable Sigma_dec : forall (c c': Sigma), {c=c'} + {c<>c'}.

  Inductive regex :=
  | Empty
  | Char (s:Sigma)
  | Or (r1:regex) (r2:regex)
  | Seq (r1:regex) (r2:regex)
  | Star (r:regex).

  Definition Eps := Star Empty.

  Inductive star (P: list Sigma -> Prop) : list Sigma -> Prop :=
  | star_empty : star P nil
  | star_iter : forall s1 s2,
      P s1 ->
      star P s2 ->
      star P (s1 ++ s2).

  Definition string_dec : forall (s s': list Sigma), {s = s'} + {s <> s'} :=
    list_eq_dec Sigma_dec.

  Fixpoint denotation (r:regex) : list Sigma -> Prop :=
    match r with
    | Empty => fun _ => False
    | Char s => fun l => l = [s]
    | Or r1 r2 => fun l => denotation r1 l \/ denotation r2 l
    | Seq r1 r2 => fun l =>
                    exists l1 l2, l = l1 ++ l2 /\
                             denotation r1 l1 /\
                             denotation r2 l2
    | Star r => fun l => star (denotation r) l
    end.

  Fixpoint observation_map (r:regex) : regex :=
    match r with
    | Empty => Empty
    | Char _ => Empty
    | Or r1 r2 => Or (observation_map r1) (observation_map r2)
    | Seq r1 r2 => Seq (observation_map r1) (observation_map r2)
    | Star r => Eps
    end.

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

  Definition derivative (c:Sigma) (P: list Sigma -> Prop) : list Sigma -> Prop :=
    fun l => P (c :: l).

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

  Hint Constructors star.

  (** characterization of observation_map: when the resulting regex
  holds, it is equivalent to Eps (an artifact of how observation_map
  is defined) and nil is in r *)

  Lemma observation_map_1 : forall r l,
      denotation (observation_map r) l ->
      l = nil.
  Proof.
    induction r; simpl; intros;
      repeat deex; subst;
        intuition.
    rewrite (IHr1 l1); eauto.
    inversion H; intuition.
  Qed.

  Lemma observation_map_2 : forall r,
      denotation (observation_map r) nil ->
      denotation r nil.
  Proof.
    induction r; simpl; intros;
      repeat deex; subst;
        intuition.
    symmetry in H; apply app_eq_nil in H; intuition subst.
    exists nil, nil; intuition.
  Qed.

  Lemma observation_map_eps : forall r l,
      denotation (observation_map r) l ->
      (l = nil /\ denotation r []).
  Proof.
    intros.
    pose proof (observation_map_1 _ _ H); subst.
    intuition auto using observation_map_2.
  Qed.

  Lemma observation_map_holds : forall r,
      denotation r nil ->
      denotation (observation_map r) nil.
  Proof.
    induction r; simpl; intros; repeat deex;
      intuition eauto.
    inversion H.
    symmetry in H; apply app_eq_nil in H; intuition subst.
    exists nil, nil; intuition eauto.
  Qed.

  Hint Resolve app_comm_cons.
  Hint Resolve observation_map_eps.

  Theorem observation_map_denotes_derivative_1 : forall r c,
      forall l, denotation (continuation_map c r) l ->
           derivative c (denotation r) l.
  Proof.
    unfold derivative.
    induction r; simpl; intros;
      intuition auto;
      repeat deex; subst.
    - destruct (Sigma_dec c s); subst; simpl in *; intuition.
      inversion H; subst; intuition eauto.
    - eauto 10.
    - pose proof (observation_map_eps _ _ H0); intuition subst.
      exists nil.
      eexists; intuition eauto.
    - repeat deex; subst.
      apply IHr in H0.
      rewrite app_comm_cons.
      eauto.
  Qed.

  Hint Resolve observation_map_holds.

  Theorem observation_map_denotes_derivative_2 : forall r c,
      forall l, derivative c (denotation r) l ->
           denotation (continuation_map c r) l.
  Proof.
    unfold derivative.
    induction r; simpl; intros;
      intuition auto;
      repeat deex; subst.
    - destruct (Sigma_dec c s); subst; simpl in *; intuition.
      inversion H; eauto.
      inversion H; eauto.
    - destruct l1; [ right | left ].
      * simpl in *; subst.
      exists nil, l; intuition eauto.
      * rewrite <- app_comm_cons in H.
        inversion H; subst.
        apply IHr1 in H0.
        exists l1, l2; intuition auto.
    - remember (c::l).
      generalize dependent l.
      induction H; intros.
      inversion Heql0.
      destruct s1; simpl in *.

      specialize (IHstar _ Heql0); repeat deex; subst.
      exists l1, l2; intuition eauto.

      inversion Heql0; subst.
      exists s1, s2; intuition eauto.
  Qed.

End RegularExpressions.