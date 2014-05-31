Require Export "Prop".

Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).

Definition funny_prop1'' := forall n, ev n -> ev (n+4).

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example :
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print and_example.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left".  apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem proj1 : forall P Q : Prop,
                  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.


(* 練習問題: ★, optional (proj2) *)

Theorem proj2 : forall P Q : Prop,
                  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ. Qed.
(* ☐ *)

Theorem and_commut : forall P Q : Prop,
                       P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
  apply HQ.
  apply HP. Qed.
