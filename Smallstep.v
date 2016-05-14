Require Export Imp.
Require Import Relations.


(* おもちゃの言語 *)

Inductive tm : Type :=
| tm_const : nat -> tm
| tm_plus : tm -> tm -> tm.

Tactic Notation "tm_cases" tactic (first) ident(c) :=
  first;
  [ Case_aux c "tm_const" | Case_aux c "tm_plus" ].

Module SimpleArith0.

Fixpoint eval (t : tm) : nat :=
  match t with
    | tm_const n => n
    | tm_plus a1 a2 => eval a1 + eval a2
  end.

End SimpleArith0.

Module SimpleArith1.

Reserved Notation " t '||' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
                tm_const n || n
  | E_Plus : forall t1 t2 n1 n2,
               t1 || n1 ->
               t2 || n2 ->
               tm_plus t1 t2 || plus n1 n2
where " t '||' n " := (eval t n).

End SimpleArith1.

Reserved Notation " t '||' t' " (at level 50, left associativity).

Inductive eval : tm -> tm -> Prop :=
  | E_Const : forall n1,
                tm_const n1 || tm_const n1
  | E_Plus : forall t1 n1 t2 n2,
               t1 || tm_const n1 ->
               t2 || tm_const n2 ->
               tm_plus t1 t2 || tm_const (plus n1 n2)
where " t '||' t' " := (eval t t').

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Const" | Case_aux c "E_Plus" ].

Module SimpleArith2.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst :
      forall n1 n2,
        tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 :
      forall t1 t1' t2,
        t1 ==> t1' ->
        tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 :
      forall n1 t2 t2',
        t2 ==> t2' ->
        tm_plus (tm_const n1) t2 ==> tm_plus (tm_const n1) t2'
where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

Example test_step_1 :
  tm_plus
    (tm_plus (tm_const 0) (tm_const 3))
    (tm_plus (tm_const 2) (tm_const 4))
    ==>
    tm_plus
    (tm_const (plus 0 3))
    (tm_plus (tm_const 2) (tm_const 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst. Qed.

(* 練習問題: ★★ (test_step_2) *)

(*
和の右側がステップを進むことができるのは、左側が終了したときだけです: もしt2が1ステップでt2'になるならば、 tm_plus (tm_const n
) t2 は1ステップで tm_plus (tm_const n) t2' になります。(次の証明を完成させなさい):
 *)

Example test_step_2 :
  tm_plus
    (tm_const 0)
    (tm_plus
       (tm_const 2)
       (tm_plus (tm_const 0) (tm_const 3)))
    ==>
    tm_plus
    (tm_const 0)
    (tm_plus
       (tm_const 2)
       (tm_const (plus 0 3))).
Proof.
  apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst.
Qed.

(* ☐ *)


Theorem step_deterministic:
  partial_function step.
Proof.
  unfold partial_function. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case; intros y2 Hy2.
    Case "ST_PlusConstConst". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". reflexivity.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2". inversion H2.
    Case "ST_Plus1". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H0 in Hy1. inversion Hy1.
      SCase "ST_Plus1".
        rewrite <- (IHHy1 t1'0).
        reflexivity. assumption.
      SCase "ST_Plus2". rewrite <- H in Hy1. inversion Hy1.
    Case "ST_Plus2". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H1 in Hy1. inversion Hy1.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2".
        rewrite <- (IHHy1 t2'0).
        reflexivity. assumption. Qed.

End SimpleArith2.


(* 値 *)

Inductive value : tm -> Prop :=
  v_const : forall n, value (tm_const n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst :
    forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2)
              ==> tm_const (plus n1 n2)
| ST_Plus1 :
    forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2
| ST_Plus2 :
    forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tm_plus v1 t2 ==> tm_plus v1 t2'

where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].


(* 練習問題: ★★★, recommended (redo_determinacy) *)

(*
この変更のサニティチェックのため、決定性を再検証しましょう。

証明スケッチ: もしxが1ステップでy1にもy2にも進むならば、 y1とy2が等しいことを示さなければならない。 step
x y1 と step x y2 の導出の最後の規則を考える。

  * もし両者ともST_PlusConstConstならば、一致は明らかである。

  * 一方が ST_PlusConstConst で、他方が ST_Plus1 または ST_Plus2 であることはあり得ない。なぜなら、そう
    なるためには、 x が tm_plus t1 t2 の形で(ST_PlusConstConstより) t1とt2が両者とも定数であり、かつt1ま
    たはt2が tm_plus ... の形でなければならない。

  * 同様に、一方が ST_Plus1 で他方が ST_Plus2 であることもあり得ない。なぜなら、そのためには、x が
    tm_plus t1 t2 の形で、 t1 は tm_plus t1 t2 の形であり、かつ( tm_const n の形であるから) 値でもなけれ
    ばならないからである。

  * 導出が両者とも ST_Plus1 または ST_Plus2 で終わるならば、帰納法の仮定から成立する。☐

証明のほとんどは前のものと同じです。しかし、練習問題の効果を最大にするために、ゼロから証明を書き、前のも
のを見るのは行き詰まった時だけにしなさい。
 *)

Theorem step_deterministic :
  partial_function step.
Proof.
  intros x y1 y2 E1.

  generalize dependent y2.

  step_cases (induction E1 as
                 [ n1 n2
                 | t1 t1' t2 TH1 ITH1
                 | v1 t2 t2' VH1 TH2 ITH2
                 ]) Case
  ; intros y2 E2.

  (* E1 is ST_PlusConstConst *)
    step_cases (inversion E2 as
                   [ dn1' dn2'
                   | dt1 dt1' dt2 dTH1
                   | dv1 dt2 dt2' [c] dTH2
                   ]; subst) SCase.
    (* E2 is ST_PlusConstConst *)
      reflexivity.
    (* E2 is ST_Plus1 *)
      inversion dTH1.
    (* E2 is ST_Plus2 *)
      inversion dTH2.
  (* E1 is ST_Plus1 *)
    step_cases (inversion E2 as
                   [ dn1' dn2'
                   | dt1 dt1' dt2 dTH1
                   | dv1 dt2 dt2' [c] dTH2
                   ]; subst) SCase.
    (* E2 is ST_PlusConstConst *)
      inversion TH1.
    (* E2 is ST_Plus1 *)
      rewrite <- (ITH1 dt1' dTH1); reflexivity.
    (* E2 is ST_Plus2 *)
      inversion TH1.
  (* E1 is ST_Plus2 *)
      step_cases (inversion E2 as
                   [ dn1' dn2'
                   | dt1 dt1' dt2 dTH1
                   | dv1 dt2 dt2' [c] dTH2
                   ]; subst) SCase.
    (* E2 is ST_PlusConstConst *)
      inversion TH2.
    (* E2 is ST_Plus1 *)
      inversion VH1; subst.
      inversion dTH1.
    (* E2 is ST_Plus2 *)
      rewrite <- (ITH2 dt2' dTH2).
      reflexivity.
Qed.

(* ☐ *)

(* 強進行と正規形 *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  tm_cases (induction t) Case.
    Case "tm_const". left. apply v_const.
    Case "tm_plus". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (tm_const (plus n n0)).
          apply ST_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (tm_plus t1 t').
          apply ST_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0].
          exists (tm_plus t' t2).
          apply ST_Plus1. apply H0.  Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall t,
  value t -> normal_form step t.
Proof.
  unfold normal_form. intros t H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
    SCase "Proof of assertion". apply strong_progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

Module Temp1.
(* Open an inner module so we can redefine value and step. *)

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n)
| v_funny : forall t1 n2,                       (* <---- *)
              value (tm_plus t1 (tm_const n2)).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tm_plus v1 t2 ==> tm_plus v1 t2'

  where " t '==>' t' " := (step t t').

(*  練習問題: ★★★, recommended (value_not_same_as_normal_form) *)
Lemma value_not_same_as_normal_form :
  exists t, value t /\ ~ normal_form step t.
Proof.
  exists (tm_plus (tm_plus (tm_const 0) (tm_const 1)) (tm_const 2)).
  split.
    (* left *) exact (v_funny (tm_plus (tm_const 0) (tm_const 1)) 2).
    (* right *)
    unfold normal_form.
    intros Contra.
    apply Contra.
    exists (tm_plus (tm_const 1) (tm_const 2)).
    apply ST_Plus1.
    exact (ST_PlusConstConst 0 1).
Qed.

(* [] *)

End Temp1.

Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,                         (* <---- *)
      tm_const n ==> tm_plus (tm_const n) (tm_const 0)
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tm_plus v1 t2 ==> tm_plus v1 t2'

  where " t '==>' t' " := (step t t').

(* 練習問題: ★★★, recommended (value_not_same_as_normal_form) *)
Lemma value_not_same_as_normal_form :
  exists t, value t /\ ~ normal_form step t.
Proof.
  exists (tm_const 1).
  split.
    (* left *) exact (v_const 1).
    (* right *)
    intros Contra.
    apply Contra.
    exists (tm_plus (tm_const 1) (tm_const 0)).
    exact (ST_Funny 1).
Qed.

(** [] *)

End Temp2.

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (tm_const n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2

  where " t '==>' t' " := (step t t').

(* 練習問題: ★★★ (value_not_same_as_normal_form') *)
Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists (tm_plus (tm_const 0) (tm_plus (tm_const 1) (tm_const 2))).
  split.
    (* left *)
    intro Contra.
    inversion Contra.

    (* right *)
    intro Contra.
    inversion Contra as [t TH] ; subst.
    inversion TH as [ | t1 t1' t2 RH PH ]; subst.
    inversion RH.
Qed.

End Temp3.

(* 練習問題 *)

Module Temp4.

Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_true : value tm_true
  | v_false : value tm_false.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tm_if t1 t2 t3 ==> tm_if t1' t2 t3

  where " t '==>' t' " := (step t t').

(* **** 練習問題: ★ (smallstep_bools) *)
(* 以下の命題のうち証明できるものはどれでしょう？
    (これは単に頭の体操です。
    しかしさらなるチャレンジとしてCoqで自分の答えを自由に証明してみなさい。) *)

Definition bool_step_prop1 :=
  tm_false ==> tm_false.

(* 証明できない *)

Example bool_step_prop1_false : ~ bool_step_prop1.
Proof.
  intros Contra.
  inversion Contra.
Qed.


Definition bool_step_prop2 :=
     tm_if
       tm_true
       (tm_if tm_true tm_true tm_true)
       (tm_if tm_false tm_false tm_false)
  ==>
     tm_true.

(* 証明できない *)

Example bool_step_prop2_false : ~ bool_step_prop2.
Proof.
  intros Contra.
  inversion Contra.
Qed.

Definition bool_step_prop3 :=
     tm_if
       (tm_if tm_true tm_true tm_true)
       (tm_if tm_true tm_true tm_true)
       tm_false
   ==>
     tm_if
       tm_true
       (tm_if tm_true tm_true tm_true)
       tm_false.

(* 証明できる *)

Example bool_step_prop3_true : bool_step_prop3.
Proof.
  apply ST_If.
  exact (ST_IfTrue tm_true tm_true).
Qed.

(* [] *)

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_true" | Case_aux c "tm_false" |
    Case_aux c "tm_if" ].

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" |
    Case_aux c "ST_If" ].

(* 練習問題: ★★★, recommended (progress_bool) *)
(* 加算式についてと同様に、ブール式についても進行定理が証明できます。
    (やってみなさい。) *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  tm_cases
    (induction t as [ | | ii iiIH it itIH ie ieIH ])
    Case.

    (* tm_true *)  left. exact v_true.
    (* tm_false *) left. exact v_false.
    (* tm_if *)
    destruct iiIH as [ iVH | iSP ].
      (* value ii *)
      destruct iVH; right.
        (* iVH true  *) exists it. exact (ST_IfTrue it ie).
        (* iVH false *) exists ie. exact (ST_IfFalse it ie).

      (* progress *)
      destruct iSP as [ ii' PH ].
      right.
      exists (tm_if ii' it ie).
      apply ST_If.
      assumption.
Qed.

(** [] *)

(* 練習問題: ★★, optional (step_deterministic) *)

Theorem step_deterministic :
  partial_function step.
Proof.
  intros x y z.
  generalize dependent z.
  generalize dependent y.
  tm_cases
    (induction x as [ | | xx IHxx xy IHxy xz IHxz ] ; intros y z HY HZ)
    Case.

    (* tm_true  *) inversion HY.
    (* tm_false *) inversion HY.

    (* tm_if *)
    tm_cases
      (destruct y) SCase.

      (* tm_true  *)
      inversion HY ; subst
      ; inversion HZ as [ | | t1 t1' t2 t3 HzP ]; subst.
        (* HY ST_IfTrue  /\ HZ ST_IfTrue  *) reflexivity.
        (* HY ST_IfTrue  /\ HZ ST_If      *) inversion HzP.
        (* HY ST_IfFalse /\ HZ ST_IfFalse *) reflexivity.
        (* HY ST_IfFalse /\ HZ ST_If      *) inversion HzP.

      (* tm_false *)
      inversion HY; subst
      ; inversion HZ as [ | | t1 t1' t2 t3 HzP ]; subst.
        (* HY ST_IfTrue  /\ HZ ST_IfFalse *) reflexivity.
        (* HY ST_IfTrue  /\ HZ ST_If      *) inversion HzP.
        (* HY ST_IfFalse /\ HZ ST_IfFalse *) reflexivity.
        (* HY ST_IfFalse /\ HZ ST_If      *) inversion HzP.

      (* tm_if *)
      inversion HY as [ | | ty1 ty1' ty2 ty3 HyP ]; subst
      ; inversion HZ as [ | | tz1 tz1' tz2 tz3 HzP ]; subst.

        (* HY ST_IfTrue  /\ HZ ST_IfTrue  *) reflexivity.
        (* HY ST_IfTrue  /\ HZ ST_If      *) inversion HzP.
        (* HY ST_IfFalse /\ HZ ST_IfFalse *) reflexivity.
        (* HY ST_IfFalse /\ HZ ST_If      *) inversion HzP.
        (* HY ST_If      /\ HZ ST_IfTrue  *) inversion HyP.
        (* HY ST_If      /\ HZ ST_IfFalse *) inversion HyP.

    rewrite -> (IHxx y1 tz1').
    reflexivity.
    assumption.
    assumption.
Qed.

(** [] *)

Module Temp5.

(* **** Exercise: 2 stars (smallstep_bool_shortcut) *)
(** **** 練習問題: ★★ (smallstep_bool_shortcut) *)
(* Suppose we want to add a "short circuit" to the step relation for
    boolean expressions, so that it can recognize when the [then] and
    [else] branches of a conditional are the same value (either
    [tm_true] or [tm_false]) and reduce the whole conditional to this
    value in a single step, even if the guard has not yet been reduced
    to a value. For example, we would like this proposition to be
    provable:
[[
         tm_if
            (tm_if tm_true tm_true tm_true)
            tm_false
            tm_false
     ==>
         tm_false.
]]
*)
(** 条件式の[then]と[else]の枝が同じ値のとき(ともに[tm_true]であるか、
    ともに[tm_false]であるかのとき)、ガードが値に簡約されていなくても、
    条件式全体を枝の値に簡約するように、ステップ関係にバイパスを追加したいとします。
    例えば次の命題を証明できるようにしたいとします:
[[
         tm_if
            (tm_if tm_true tm_true tm_true)
            tm_false
            tm_false
     ==>
         tm_false.
]]
*)

(* Write an extra clause for the step relation that achieves this
    effect and prove [bool_step_prop4]. *)
(** ステップ関係にこのための追加の節を記述し、[bool_step_prop4]を証明しなさい。*)

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tm_if t1 t2 t3 ==> tm_if t1' t2 t3
(* FILL IN HERE *)
  | ST_IfShortCircuit :
      forall t1 t2,
        value t2 ->
        tm_if t1 t2 t2 ==> t2
  where " t '==>' t' " := (step t t').
(** [] *)

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" |
    Case_aux c "ST_If" |
    Case_aux c "ST_IfShortCircuit"  ].

Definition bool_step_prop4 :=
         tm_if
            (tm_if tm_true tm_true tm_true)
            tm_false
            tm_false
     ==>
         tm_false.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  apply ST_IfShortCircuit.
  exact v_false.
Qed.
(** [] *)

(* **** Exercise: 3 stars (properties_of_altered_step) *)
(** **** 練習問題: ★★★ (properties_of_altered_step) *)
(* It can be shown that the determinism and strong progress theorems
    for the step relation in the lecture notes also hold for the
    definition of step given above.  After we add the clause
    [ST_ShortCircuit]...

    - Is the [step] relation still deterministic?  Write yes or no and
      briefly (1 sentence) explain your answer.

      Optional: prove your answer correct in Coq.
*)
(** 講義ノートのステップ関係についての決定性定理と強進行定理が、
    上記のステップの定義についても証明できます。
    [ST_ShortCircuit]節を追加した後で...

    - [step]関係はそれでも決定性を持つでしょうか？
      yes または no と書き、簡潔に(1文で)その答えを説明しなさい。

      Optional: Coq でその答えが正しいことを証明しなさい。
*)

(*
 no.

 条件節が normal form かつ short circuit が可能なときに、条件節を簡約するのと short ciruit を行うのとで 2通りの簡約方法があるから。
 *)

Theorem step_non_deterministic :
  ~ partial_function step.
Proof.
  intros Hpf.

  (* tm_if (tm_if tm_true tm_true tm_true) tm_false tm_false *)
  (* tm_if tm_true tm_false tm_false *)
  (* tm_false *)

  assert (tm_if tm_true tm_false tm_false = tm_false) as NH.

    apply (Hpf
             (tm_if (tm_if tm_true tm_true tm_true) tm_false tm_false)
             (tm_if tm_true tm_false tm_false)
             tm_false).
      apply ST_If. exact (ST_IfTrue tm_true tm_true).
      apply ST_IfShortCircuit.
      exact v_false.
      discriminate NH.
Qed.

(*
   - Does a strong progress theorem hold? Write yes or no and
     briefly (1 sentence) explain your answer.

     Optional: prove your answer correct in Coq.
*)
(**
   - 強進行定理は成立するでしょうか？
     yes または no と書き、簡潔に(1文で)その答えを説明しなさい。

      Optional: Coq でその答えが正しいことを証明しなさい。
*)

(*
 yes.

 value で簡約できるものは無く、value でなければ簡約できるので、強進行が成立する。
 *)

Theorem strong_progress :
  forall t, value t \/ (exists t', t ==> t').
Proof.
  tm_cases (induction t as [ | | ti tt te ]) Case.

    left. exact v_true.
    left. exact v_false.

    right.
      destruct tt as [ [ | ] | HP ].
        exists te. exact (ST_IfTrue  te t1).
        exists t1. exact (ST_IfFalse te t1).

        destruct HP as [ pti HP' ].
        exists (tm_if pti te t1).
        apply ST_If.
        assumption.
Qed.

(*
   - In general, is there any way we could cause strong progress to
     fail if we took away one or more constructors from the original
     step relation? Write yes or no and briefly (1 sentence) explain
     your answer.

  (* FILL IN HERE *)
*)
(**
   - 一般に、オリジナルのステップ関係から1つ以上のコンストラクタを取り除いて、
     強進行性を持たなくする方法はあるでしょうか？
     yes または no と書き、簡潔に(1文で)その答えを説明しなさい。

  (*
   yes.

   value になっていない
   *)
*)
(** [] *)

End Temp5.
End Temp4.

(* マルチステップ簡約 *)

(* マルチステップ簡約 *)

Definition stepmany := refl_step_closure step.

Notation " t '==>*' t' " := (stepmany t t') (at level 40).

Lemma test_stepmany_1:
      tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
   ==>*
      tm_const (plus (plus 0 3) (plus 2 4)).
Proof.
  apply rsc_step with
            (tm_plus
                (tm_const (plus 0 3))
                (tm_plus (tm_const 2) (tm_const 4))).
  apply ST_Plus1. apply ST_PlusConstConst.
  apply rsc_step with
            (tm_plus
                (tm_const (plus 0 3))
                (tm_const (plus 2 4))).
  apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  apply rsc_R.
  apply ST_PlusConstConst.  Qed.

Lemma test_stepmany_1':
      tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
  ==>*
      tm_const (plus (plus 0 3) (plus 2 4)).
Proof.
  eapply rsc_step. apply ST_Plus1. apply ST_PlusConstConst.
  eapply rsc_step. apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  eapply rsc_step. apply ST_PlusConstConst.
  apply rsc_refl.  Qed.


(* **** 練習問題: ★ (test_stepmany_2) *)
Lemma test_stepmany_2:
  tm_const 3 ==>* tm_const 3.
Proof.
  apply rsc_refl.
Qed.

(* [] *)

(* **** 練習問題: ★ (test_stepmany_3) *)
Lemma test_stepmany_3:
      tm_plus (tm_const 0) (tm_const 3)
   ==>*
      tm_plus (tm_const 0) (tm_const 3).
Proof.
  apply rsc_refl.
Qed.

(* [] *)

(* **** 練習問題: ★★ (test_stepmany_4) *)
Lemma test_stepmany_4:
      tm_plus
        (tm_const 0)
        (tm_plus
          (tm_const 2)
          (tm_plus (tm_const 0) (tm_const 3)))
  ==>*
      tm_plus
        (tm_const 0)
        (tm_const (plus 2 (plus 0 3))).
Proof.
  eapply rsc_step.
    apply ST_Plus2. exact (v_const 0).
    apply ST_Plus2. exact (v_const 2).
    apply ST_PlusConstConst.
  eapply rsc_step.
    apply ST_Plus2. exact (v_const 0).
    apply ST_PlusConstConst.
  eapply rsc_refl.
Qed.

(** [] *)

(* 正規形再び *)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').


(* **** 練習問題: ★★★, optional (test_stepmany_3) *)
Theorem normal_forms_unique:
  partial_function normal_form_of.
Proof.
  unfold partial_function. unfold normal_form_of.  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12]. destruct P2 as [P21 P22].
  generalize dependent y2.

  unfold stepmany in P11.

  rsc_cases (induction P11) Case
  ; intros y2 P21 P22
  ; rsc_cases (destruct P21) SCase.

    (* P11 is rsc_refl *)
    + (* P21 is rsc_refl *)
      reflexivity.

    + (* P21 is rsc_step *)
      elim P12.
      exists y.
      assumption.

    (* P11 is rsc_step *)
    + (* P21 is rsc_refl *)
      elim P22.
      exists y.
      assumption.

    + (* P21 is rsc_step *)
      eapply IHP11.
      assumption.
      apply (step_deterministic x y0 y) in H0; subst.
      assumption.
      assumption.
      assumption.
Qed.

(*
 *)

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (refl_step_closure R) t t' /\ normal_form R t'.


Lemma stepmany_congr_1 : forall t1 t1' t2,
     t1 ==>* t1' ->
     tm_plus t1 t2 ==>* tm_plus t1' t2.
Proof.
  intros t1 t1' t2 H. rsc_cases (induction H) Case.
    Case "rsc_refl". apply rsc_refl.
    Case "rsc_step". apply rsc_step with (tm_plus y t2).
        apply ST_Plus1. apply H.
        apply IHrefl_step_closure. Qed.

(** **** 練習問題: ★★ *)
Lemma stepmany_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     tm_plus t1 t2 ==>* tm_plus t1 t2'.
Proof.
  intros t1 t2 t2' V1 M2.

  rsc_cases (induction M2) Case.
  - apply rsc_refl.
  - apply rsc_step with (tm_plus t1 y).
    apply ST_Plus2.
    assumption.
    assumption.
    assumption.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  tm_cases (induction t) Case.
    Case "tm_const".
      exists (tm_const n).
      split.
      SCase "l". apply rsc_refl.
      SCase "r".
        (* We can use [rewrite] with "iff" statements, not
           just equalities: *)
        rewrite nf_same_as_value. apply v_const.
    Case "tm_plus".
      destruct IHt1 as [t1' H1]. destruct IHt2 as [t2' H2].
      destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
      rewrite nf_same_as_value in H12. rewrite nf_same_as_value in H22.
      inversion H12 as [n1]. inversion H22 as [n2].
      rewrite <- H in H11.
      rewrite <- H0 in H21.
      exists (tm_const (plus n1 n2)).
      split.
        SCase "l".
          apply rsc_trans with (tm_plus (tm_const n1) t2).
          apply stepmany_congr_1. apply H11.
          apply rsc_trans with
             (tm_plus (tm_const n1) (tm_const n2)).
          apply stepmany_congr_2. apply v_const. apply H21.
          apply rsc_R. apply ST_PlusConstConst.
        SCase "r".
          rewrite nf_same_as_value. apply v_const.  Qed.


(* ビッグステップ簡約とスモールステップ簡約の同値性 *)


Lemma eval__value : forall t1 t2,
     eval t1 t2 ->
     value t2.
Proof.
  intros t1 t2 HE.
  eval_cases (inversion HE) Case; apply v_const.  Qed.


(* **** Exercise: 3 stars (eval__stepmany) *)
(** **** 練習問題: ★★★ (eval__stepmany) *)
(* You'll want to use the congruences and some properties of
    [rsc] for this. *)
(** この証明のために合同と[rsc]のいくつかの性質を使うのが良いでしょう。*)

Theorem eval__stepmany : forall t v,
  eval t v -> t ==>* v.
Proof.
  intros t v EH.

  eval_cases (induction EH) Case.
  - Case "E_Const".
    apply rsc_refl.

  - Case "E_Plus".
    eapply rsc_trans.
    eapply stepmany_congr_1.
    eassumption.

    eapply rsc_trans.
    eapply stepmany_congr_2.
    exact (v_const n1).
    eassumption.

    eapply rsc_step.
    eapply ST_PlusConstConst.
    apply rsc_refl.
Qed.

(** [] *)

(* **** Exercise: 3 stars (eval__stepmany_inf) *)
(** **** 練習問題: ★★★ (eval__stepmany_inf) *)
(* Write an informal version of the proof of eval__stepmany.

(* FILL IN HERE *)
[]
*)
(** eval__stepmany の証明の非形式版を記述しなさい。

(* ここを埋めなさい *)
[]
*)

(* **** Exercise: 3 stars (step__eval) *)
(** **** 練習問題: ★★★ (step__eval) *)
Theorem step__eval : forall t t' v,
     t ==> t' ->
     t' || v ->
     t || v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


Theorem stepmany__eval : forall t v,
  normal_form_of t v -> t || v.
Proof.
  intros t v Hnorm.
  unfold normal_form_of in Hnorm.
  inversion Hnorm as [Hs Hnf]; clear Hnorm.
  (* v is a normal form -> v = tm_const n for some n *)
  rewrite nf_same_as_value in Hnf. inversion Hnf. clear Hnf.
  rsc_cases (induction Hs) Case; subst.
  Case "rsc_refl".
    apply E_Const.
  Case "rsc_step".
    eapply step__eval. eassumption. apply IHHs. reflexivity.  Qed.


Corollary stepmany_iff_eval : forall t v,
  normal_form_of t v <-> t || v.
Proof.
  split.
  Case "->". apply stepmany__eval.
  Case "<-". unfold normal_form_of. intros E. split. apply eval__stepmany.
    assumption. rewrite nf_same_as_value. eapply eval__value. eassumption.  Qed.


(** さらなる練習問題 *)


(* **** Exercise: 4 stars (combined_properties) *)
(** **** 練習問題: ★★★★ (combined_properties) *)
(* We've considered the arithmetic and conditional expressions
    separately.  This exercise explores how the two interact. *)
(** ここまでに算術式と条件式を別々に考えてきました。
    この練習問題ではこの2つがどのように相互作用するかを調べます。*)

Module Combined.

Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_const" | Case_aux c "tm_plus"
  | Case_aux c "tm_true" | Case_aux c "tm_false" | Case_aux c "tm_if" ].

Inductive value : tm -> Prop :=
  | v_const : forall n, value (tm_const n)
  | v_true : value tm_true
  | v_false : value tm_false.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tm_plus v1 t2 ==> tm_plus v1 t2'
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tm_if t1 t2 t3 ==> tm_if t1' t2 t3

  where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2"
  | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

(** 前には、plus式とif式について、以下のことを別々に証明しました...

    - ステップ関係が部分関数であること(つまり、決定性を持つこと)。

    - すべての項が値であるか、1ステップ進むことができるかを主張する強進行補題。

    結合した言語について、これらの性質を証明、または反証しなさい。*)

Lemma value_is_nf : forall t,
  value t -> normal_form step t.
Proof.
  intros t H. inversion H.
  - intros contra. inversion contra. inversion H1.
  - intros contra. inversion contra. inversion H1.
  - intros contra. inversion contra. inversion H1.
Qed.

Theorem step_deterministic:
  partial_function step.
Proof.
  intros x y z YH ZH.
  generalize dependent z.

  step_cases (induction YH) Case
  ; intros z ZH.

  - Case "ST_PlusConstConst".
    inversion ZH; subst.
    + reflexivity.
    + inversion H2.
    + inversion H3.

  - Case "ST_Plus1".
    inversion ZH; subst.

    + inversion YH.

    + rewrite <- (IHYH t1'0).
      reflexivity.
      assumption.

    + elim (value_is_nf t1 H1).
      exists t1'.
      assumption.

  - Case "ST_Plus2".
    inversion ZH; subst.

    + inversion YH.

    + elim (value_is_nf v1 H).
      exists t1'.
      assumption.

    + rewrite <- (IHYH t2'0).
      reflexivity.
      assumption.

  - Case "ST_IfTrue".
    inversion ZH.

    + reflexivity.

    + inversion H3.

  - Case "ST_IfFalse".
    inversion ZH.

    + reflexivity.

    + inversion H3.

  - Case "ST_If".
    inversion ZH; subst.

    + inversion YH.

    + inversion YH.

    + rewrite <- (IHYH t1'0).
      reflexivity.
      assumption.
Qed.

Theorem not_strong_progress :
  ~ (forall t, value t \/ (exists t', t ==> t')).
Proof.
  intros contra.

  destruct (contra (tm_plus tm_true tm_true)).
  - inversion H.
  - destruct H.
    inversion H.
    + inversion H3.
    + inversion H4.
Qed.

End Combined.


(* スモールステップ Imp *)


Inductive aval : aexp -> Prop :=
  av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '==>a' t' " (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
    AId i / st ==>a ANum (st i)
  | AS_Plus : forall st n1 n2,
    APlus (ANum n1) (ANum n2) / st ==>a ANum (plus n1 n2)
  | AS_Plus1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (APlus a1 a2) / st ==>a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (APlus v1 a2) / st ==>a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
    (AMinus (ANum n1) (ANum n2)) / st ==>a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (AMinus a1 a2) / st ==>a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (AMinus v1 a2) / st ==>a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
    (AMult (ANum n1) (ANum n2)) / st ==>a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (AMult (a1) (a2)) / st ==>a (AMult (a1') (a2))
  | AS_Mult2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (AMult v1 a2) / st ==>a (AMult v1 a2')

  where " t '/' st '==>a' t' " := (astep st t t').

Reserved Notation " t '/' st '==>b' t' " (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
  | BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st ==>b
    (if (beq_nat n1 n2) then BTrue else BFalse)
  | BS_Eq1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (BEq a1 a2) / st ==>b (BEq a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (BEq v1 a2) / st ==>b (BEq v1 a2')
  | BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st ==>b
             (if (ble_nat n1 n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (BLe a1 a2) / st ==>b (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (BLe v1 a2) / st ==>b (BLe v1 (a2'))
  | BS_NotTrue : forall st,
    (BNot BTrue) / st ==>b BFalse
  | BS_NotFalse : forall st,
    (BNot BFalse) / st ==>b BTrue
  | BS_NotStep : forall st b1 b1',
    b1 / st ==>b b1' ->
    (BNot b1) / st ==>b (BNot b1')
  | BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st ==>b BTrue
  | BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st ==>b BFalse
  | BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st ==>b BFalse
  | BS_AndTrueStep : forall st b2 b2',
    b2 / st ==>b b2' ->
    (BAnd BTrue b2) / st ==>b (BAnd BTrue b2')
  | BS_AndStep : forall st b1 b1' b2,
    b1 / st ==>b b1' ->
    (BAnd b1 b2) / st ==>b (BAnd b1' b2)

  where " t '/' st '==>b' t' " := (bstep st t t').

Reserved Notation " t '/' st '==>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
    a / st ==>a a' ->
    (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
    (i ::= (ANum n)) / st ==> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
    c1 / st ==> c1' / st' ->
    (c1 ; c2) / st ==> (c1' ; c2) / st'
  | CS_SeqFinish : forall st c2,
    (SKIP ; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
    IFB BTrue THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
    IFB BFalse THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
    b / st ==>b b' ->
    IFB b THEN c1 ELSE c2 FI / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
        (WHILE b DO c1 END) / st
    ==> (IFB b THEN (c1; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

(* 並列実行 Imp *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "PAR" ].

Notation "'SKIP'" :=
  CSkip.
Notation "l '::=' a" :=
  (CAss l a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
    a / st ==>a a' ->
    (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
    (i ::= (ANum n)) / st ==> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
    c1 / st ==> c1' / st' ->
    (c1 ; c2) / st ==> (c1' ; c2) / st'
  | CS_SeqFinish : forall st c2,
    (SKIP ; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
    (IFB BTrue THEN c1 ELSE c2 FI) / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
    (IFB BFalse THEN c1 ELSE c2 FI) / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
    b /st ==>b b' ->
    (IFB b THEN c1 ELSE c2 FI) / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
    (WHILE b DO c1 END) / st ==>
             (IFB b THEN (c1; (WHILE b DO c1 END)) ELSE SKIP FI) / st
  (* New: *)
  | CS_Par1 : forall st c1 c1' c2 st',
    c1 / st ==> c1' / st' ->
    (PAR c1 WITH c2 END) / st ==> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
    c2 / st ==> c2' / st' ->
    (PAR c1 WITH c2 END) / st ==> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
    (PAR SKIP WITH SKIP END) / st ==> SKIP / st
  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cstepmany := refl_step_closure cstep.

Notation " t '/' st '==>*' t' '/' st' " :=
   (refl_step_closure cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

Definition par_loop : com :=
  PAR
    Y ::= ANum 1
  WITH
    WHILE BEq (AId Y) (ANum 0) DO
      X ::= APlus (AId X) (ANum 1)
    END
  END.

Example par_loop_example_0:
  exists st',
       par_loop / empty_state  ==>* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply rsc_step. apply CS_Par1.
    apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse.
  eapply rsc_step. apply CS_ParDone.
  eapply rsc_refl.
  reflexivity. Qed.

Example par_loop_example_2:
  exists st',
       par_loop / empty_state ==>* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfTrue.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_SeqFinish.

  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfTrue.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply rsc_step. apply CS_Par1. apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_SeqFinish.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse.
  eapply rsc_step. apply CS_ParDone.
  eapply rsc_refl.
  reflexivity. Qed.

(* より一般に... *)

(* **** 練習問題: ★★★, optional *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>* par_loop / (update st X (S n)).
Proof.
  intros n st [Xn Y0].
  unfold par_loop.
  eapply rsc_step. eapply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  rewrite Y0.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfTrue.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_SeqFinish.

  (* unfold par_loop. *)
  rewrite -> Xn. rewrite plus_comm. simpl.
  eapply rsc_refl.
Qed.


(* **** 練習問題: ★★★, optional *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_state ==>*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_state).
    split; unfold update; reflexivity.

  rename x into st.
  destruct H as [H' [HX HY]].
  exists (update st Y 1). split.
  eapply rsc_trans with (par_loop,st). apply H'.
  eapply rsc_step. apply CS_Par1. apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite update_eq.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse.
  eapply rsc_step. apply CS_ParDone.
  apply rsc_refl.

  rewrite update_neq. assumption. reflexivity.
Qed.

End CImp.
