(* 関係の性質 *)

Require Export Logic.

(* 関係の基本性質 *)

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
  apply IHn1. assumption.

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

(* ☐ *)

(* 練習問題:★★, optional *)

(*
同じことを、oについての帰納法で証明しなさい。
 *)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].

  (* 0 *) inversion Hmo.
  (* S o' *)
    induction Hmo as [| o2].
    (* destruct o' as [| o2]. *)
    (* m = o' *) apply le_S. apply Hnm.
    (* m = S o2 *) apply le_S. apply IHHmo.

    (* apply le_trans with (a := (S n)) (b := (S m)) (c := (S o')). *)
    (* (* nm *) apply le_S. apply Hnm. *)
    (* (* mo' *) apply Hmo. *)
Qed.

(* ☐ *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  apply le_S. apply le_n.
  apply H. Qed.

(* 練習問題:★, optional *)

Lemma le_le_Sn :
  forall n m, n <= S m -> n <= m \/ n = S m.
Proof.
  intros n m HnSm.

  inversion HnSm.
  (* le_n *) right. reflexivity.
  (* le_S *) left.  apply H0.
Qed.

Theorem le_S_n :
  forall n m, (S n <= S m) -> (n <= m).
Proof.
  intros n m H.

  assert (S n <= m \/ S n = S m).
  apply le_le_Sn with (n := (S n)).
  assumption.

  inversion H0.
  (* S n <= m*)
    apply le_Sn_le.
    assumption.
  (* S n = S m *)
    inversion H1.
    apply le_n.
Qed.

(* ☐ *)

(* 練習問題:★★, optional(le_Sn_n_inf) *)

(*
以下の定理の非形式的な証明を示しなさい。

定理: すべてのnについて、~(S n <= n)

形式的な証明は後のoptionalな練習問題ですが、ここでは、形式的な証明を行わずに、まず非形式的な証明を示しなさい。
 *)

(*
証明:
 *)

(* ☐ *)


(* 練習問題:★, optional *)

Theorem le_Sn_n :
  forall n, ~ (S n <= n).
Proof.
  intros n NH.
  induction n as [| n1].
  (* 0 *) inversion NH.
  (* S n1*)
    apply IHn1.
    apply le_S_n.
    assumption.
Qed.

(* ☐ *)


Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).


(* 練習問題:★★, optional *)

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold symmetric.
  intros contra.
  assert (1 <= 0) as NH10.
  apply contra.
  apply le_S.
  apply le_n.
  inversion NH10.
Qed.

(* ☐ *)


Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* 練習問題:★★, optional *)

Lemma le_eq_or_lt :
  forall n m, n <= m -> n = m \/ n < m.
Proof.
  intros n m Hnm.
  inversion Hnm.
  (* le_n *) left. reflexivity.
  (* le_S *)
    right. unfold lt.
    apply n_le_m__Sn_le_Sm.
    assumption.
Qed.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  intros a b LH RH.

  inversion LH as [ | a1 Hab ].
  reflexivity.

  assert (S a1 <= a1).
  apply le_trans with a.
  rewrite -> H.
  assumption.
  assumption.

  apply le_Sn_n in H0.
  inversion H0.
Qed.

(* ☐ *)

(* 練習問題:★★, optional *)

Theorem le_step :
  forall n m p,
    n < m -> m <= S p -> n <= p.
Proof.
  intros n m p Hnm Hmp1.
  unfold lt in Hnm.

  assert (S n <= S p).
  apply le_trans with m.
  assumption.
  assumption.

  apply le_S_n.
  assumption.
Qed.

(* ☐ *)


Definition equivalence {X: Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X: Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X: Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
  Case "refl". apply le_reflexive.
  split.
    Case "antisym". apply le_antisymmetric.
    Case "transitive". apply le_trans. Qed.


(* 反射推移閉包 *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step : forall x y, R x y -> clos_refl_trans R x y
  | rt_refl : forall x, clos_refl_trans R x x
  | rt_trans : forall x y z,
                 clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.

Theorem next_nat_closure_is_le :
  forall n m,
    (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  Case "->".
    intro H. induction H.
      apply rt_refl.
      apply rt_trans with m. apply IHle. apply rt_step. apply nn.
  Case "<-".
    intro H. induction H.
      SCase "rt_step". inversion H. apply le_S. apply le_n.
      SCase "rt_refl". apply le_n.
      SCase "rt_trans".
        apply le_trans with y.
        apply IHclos_refl_trans1.
        apply IHclos_refl_trans2. Qed.

Inductive refl_step_closure {X: Type} (R: relation X)
        : X -> X -> Prop :=
  | rsc_refl : forall (x : X),
                 refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                 R x y ->
                 refl_step_closure R y z ->
                 refl_step_closure R x z.

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl"
  | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
                  R x y -> refl_step_closure R x y.
Proof.
  intros X R x y r.
  apply rsc_step with y. apply r. apply rsc_refl. Qed.

(* 練習問題:★★, optional(rsc_trans) *)

Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  intros X R x y z Hxy Hyz.
  rsc_cases (induction Hxy as [x| x y y' Rxy Hyy ]) Case.
  (* refl *) assumption.
  (* step *)
    apply rsc_step with y.
    assumption.
    apply IHHyy. assumption.
Qed.

(* ☐ *)

(* 練習問題:★★★, optional (rtc_rsc_coincide) *)

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  intros X R x y.
  split; intro H.

  (* -> *)
    rt_cases (induction H as [x y Rxy | x | x y' y Hxy' IHxy' Hy'y IHy'y ]) Case.


    (* rt_step *)
      apply rsc_step with y. assumption.
      apply rsc_refl.

    (* rt_refl *)
      apply rsc_refl.

    (* rt_trans *)
      apply rsc_trans with y'; assumption.

  (* <- *)
    rsc_cases (induction H as [x | x y' y Rxy' Hy'y IHy'y ]) Case.

    (* rsc_refl *)
      apply rt_refl.

    (* rsc_step *)
      apply rt_trans with y'.
      apply rt_step. assumption.
      assumption.
Qed.
(* ☐ *)
