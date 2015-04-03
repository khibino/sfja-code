Require Export Logic.

Definition relation (X: Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 P Q.
  inversion P. inversion Q.
  reflexivity. Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros H.
  assert (0 = 1) as Nonsense.
  Case "Proof of assertion".
  apply H with 0.
    apply le_n.
    apply le_S. apply le_n.
    inversion Nonsense. Qed.

(* 練習問題:★★, optional *)

(*
Logic_J.v に定義された total_relation が部分関数ではないことを示しなさい。
 *)

Print total_relation.

Theorem total_relation_le_not_a_partial_function :
  ~ (partial_function (total_relation le)).
Proof.
  unfold partial_function.
  intros H.
  assert (0 = 1) as Nonsense.
  apply H with 0.
  split; left; apply le_n.
  split. left. apply le_S. apply le_n.
  inversion Nonsense.
Qed.

Theorem empty_relation_not_a_partial_function :
  partial_function empty_relation.
Proof.

  assert (forall n, ~ (S (S n) = n)) as NE2.
  intros n E.
  induction n as [| n1].
  (* 0 *)
  inversion E.
  (* S n1 *)
  inversion E.
  apply IHn1. exact H0.

  unfold partial_function.
  intros x y1 y2 P Q.

  inversion P as [ [ HL HR ] ].
  rewrite <- HL in HR.

  apply ex_falso_quodlibet.
  apply (NE2 x). apply HR.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.


Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo. Qed.

Theorem lt_trans :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(* 練習問題:★★, optional *)

(*
lt_trans は、帰納法を使って手間をかければ、le_trans を使わずに証明することができます。これをやってみなさい。
 *)

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  (* le_n *) apply le_S. apply Hnm.
  (* le_S *) apply le_S. apply IHHm'o. Qed.
