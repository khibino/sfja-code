
(* Coq スタンダードライブラリから *)

Require Omega. Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.

(* Basics.vから *)

Definition admit {T: Type} : T. Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
    | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr (v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
    clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
      set (x := name); move_to_top x
    | assert_eq x name; move_to_top x
    | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 :
  forall b c, andb b c = true -> b = true.
 Proof.
   intros b c H.
   destruct b.
   Case "b = true".
     reflexivity.
   Case "b = false".
     rewrite <- H. reflexivity. Qed.

Theorem andb_true_elim2 :
  forall b c, andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
    SCase "b = true".
      reflexivity.
    SCase "b = false".
      reflexivity. Qed.

Theorem beq_nat_sym :
  forall n m : nat, beq_nat n m = beq_nat m n.
Proof.
  induction n as [| n'].
  (* n = 0 *)
    destruct m as [| m'].
    (* m = 0 *) reflexivity.
    (* m = S m' *)
      simpl. reflexivity.
  (* n = S n' *)
      destruct m as [| m'].
      (* m = 0 *) simpl. reflexivity.
      (* m = S m' *)
        simpl.
        apply (IHn' m').
Qed.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* Props.vから *)

Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n:nat, ev n -> ev (S (S n)).

(* Logic.vから *)

Theorem andb_true :
  forall b c, andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H. Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra. Qed.

Theorem not_eq_beq_false :
  forall n n' : nat, n <> n' -> beq_nat n n' = false.
Proof.
  induction n as [| k].
  (* n = 0 *)
    destruct n' as [| k'].
    (* n' = 0 *)
      intros H.
      apply ex_falso_quodlibet. apply H.
      reflexivity.
    (* n = S k' *)
      intros H. reflexivity.
  (* n = S k *)
    destruct n' as [| k'].
    (* n = 0 *) intros H. reflexivity.
    (* n = S n' *)
      intros H. simpl.
      apply IHk.
      intros eq.
      apply H.
      rewrite <- eq.
      reflexivity.
Qed.

Theorem ev_not_ev_S :
  forall n, ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H.
  (* ev_0 *)  intro H. inversion H.
  (* ev_SS *)
    intro H2.
    inversion H2 as [| n' evH ].
    apply (IHev evH).
Qed.

Lemma O_le_n :
  forall n, 0 <= n.
Proof.
  induction n as [| n'].
  apply le_n.
  apply le_S.
  apply IHn'.
Qed.

Lemma le_dec_R :
  forall {n m}, n <= S m -> n <= m \/ n = S m.
(* -> *)
Proof.
  intros n m H0.
  inversion H0 as [ eq | m' H1 eq ].
  (* le_n *) right. reflexivity.
  (* le_S *) left.  exact H1.
Qed.

Lemma le_dec_L :
  forall {n m}, n <= m \/ n = S m -> n <= S m.
(* <- *)
Proof.
  intros n m H.
  destruct H as [LE | EQ].
  (* le *) apply (le_S n m LE).
  (* eq *) rewrite <- EQ. apply le_n.
Qed.

Lemma le_dec :
  forall {n m}, n <= S m <-> n <= m \/ n = S m.
Proof.
  split. apply le_dec_R. apply le_dec_L.
Qed.

Lemma n_le_m__Sn_le_Sm :
  forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [EQ | m' LE].
  (* EQ *) apply le_n.
  (* LE *) apply le_S. apply IHLE.
Qed.

Lemma Sn_le_Sm__n_le_m :
  forall n m, S n <= S m -> n <= m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m'].
  (* m = 0 *)
    intros n H.
    inversion H as [eq | m' L].
    (* le_n *) apply le_n.
    (* le_S *) inversion L.

  (* m = S m' *)
    intros n H.
    destruct (le_dec_R H) as [LE | EQ].
    (* S n <= S m' *) apply le_S. apply IHm'. apply LE.
    (* S n = S (S m') *) inversion EQ as [ EQ1 ]. apply le_n.
Qed.

Theorem ble_nat_true :
  forall n m, ble_nat n m = true -> n <= m.
Proof.
  induction n as [| n'].
  (* n = 0 *) intros m H. apply O_le_n.
  (* n = S n' *)
    destruct m as [| m'].
    (* m = 0 *) intros H. inversion H.
    (* m = S m' *)
      simpl. intros H.
      apply n_le_m__Sn_le_Sm. apply IHn'.  apply H.
Qed.

Theorem ble_nat_false :
  forall n m, ble_nat n m = false -> ~ (n <= m).
Proof.
  induction n as [| n'].
  (* n = 0 *)
    destruct m as [| m'].
    (* 0 *)    simpl. intro H. inversion H.
    (* S m' *) simpl. intro H. inversion H.
  (* n = S n' *)
    intros m H.
    destruct m as [| m'].
    (* 0 *) intro LE. inversion LE.
    (* S m' *)
      simpl in H.
      intro LE.
      apply Sn_le_Sm__n_le_m in LE.
      apply (IHn' m').
      apply H. apply LE.
Qed.
