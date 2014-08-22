
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
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  (* m = 0 *)
    destruct n as [| n' ].
    (* n = 0 *)
      intros H.
      apply ex_falso_quodlibet. apply H.
      reflexivity.
    (* n = S n' *)
      intros H. reflexivity.
  (* m = S m' *)
    destruct n as [| n' ].
    (* n = 0 *) intros H. reflexivity.
    (* n = S n' *)
      intros H. simpl.
      apply IHm'.
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

(*
Theorem ble_nat_true :
  forall n m, ble_nat n m = true -> n <= m.
Proof.
  induction n as [| n'].
  (* n = 0 *)
    induction m as [| m'].
    (* m = 0 *) intro H. apply le_n.
    (* m = S m' *)
      simpl. intro H. apply le_S.

Admitted.
 *)

(*
Theorem ble_nat_false :
  forall n m, ble_nat n m = false -> ~ (n <= m).
Admitted.
 *)
