
Require Export Imp.

(* 宿題割当てについての一般的アドバイス *)

(* 振る舞い同値性 *)

(* 定義 *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state), aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state), beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st':state), (c1 / st || st') <-> (c2 / st || st').

(* 練習問題: ★★, optional (pairs_equiv) *)

(*
以下のプログラムの対の中で、同値なのはどれでしょうか？それぞれに
ついて、"yes" か "no" を書きなさい。
 *)

(*
(a)
    WHILE (BLe (ANum 1) (AId X)) DO
      X ::= APlus (AId X) (ANum 1)
    END

と
    WHILE (BLe (ANum 2) (AId X)) DO
      X ::= APlus (AId X) (ANum 1)
    END
 *)

(* no - 初期値 X = 1 のときに異なる *)

(*
(b)
    WHILE BTrue DO
      WHILE BFalse DO X ::= APlus (AId X) (ANum 1) END
    END

と
    WHILE BFalse DO
      WHILE BTrue DO X ::= APlus (AId X) (ANum 1) END
    END
 *)

(* no - 上はループするが、下はループしない *)

(* ☐ *)

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. apply minus_diag.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

Theorem skip_left: forall c,
  cequiv
     (SKIP; c)
     c.
Proof.
  intros c st st'.
  split; intros H.
  Case "->".
    inversion H. subst.
    inversion H2. subst.
    assumption.
  Case "<-".
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.


(* 練習問題: ★★ (skip_right) *)

Theorem skip_right: forall c,
  cequiv
    (c; SKIP)
    c.
Proof.
  intros c st st'.
  split.

  (* -> *)
    intros H.
    inversion H. subst.
    inversion H5. subst.
    assumption.

  (* <- *)
    intros H.
    apply E_Seq with st'.
    assumption.
    apply E_Skip.
Qed.

(* ☐ *)

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  Case "->".
    inversion H; subst. assumption. inversion H5.
  Case "<-".
    apply E_IfTrue. reflexivity. assumption. Qed.

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      assumption.
    SCase "b evaluates to false (contradiction)".
      rewrite Hb in H5.
      inversion H5.
  Case "<-".
    apply E_IfTrue; try assumption.
    rewrite Hb. reflexivity. Qed.

(* 練習問題: ★★, recommended (IFB_false) *)

Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros b c1 c2 Hb.
  split.

  (* -> *)
    intros H.
    inversion H ; subst.
    rewrite Hb in H5.
    (* beval st BFalse = true *) inversion H5.
    (* beval st BFalse = false *) assumption.

  (* <- *)
    intros H.
    apply E_IfFalse.
    (* if *)   rewrite Hb. reflexivity.
    (* else *) assumption.
Qed.
(* ☐ *)

(* 練習問題: ★★★ (swap_if_branches) *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2.
  split.

  (* -> *)
    intros H.
    inversion H ; subst.

    (* b === BTrue *)
    apply E_IfFalse.
    (* if *)   simpl. rewrite H5. reflexivity.
    (* else *) assumption.

    (* b === BFalse *)
    apply E_IfTrue.
    (* if *)   simpl. rewrite H5. reflexivity.
    (* then *) assumption.

  (* <- *)
    intros H.
    inversion H ; subst.

    (* b === BFalse *)
    simpl in H5.
    apply negb_true_iff in H5.
    apply E_IfFalse.
    (* if *)   assumption.
    (* else *) assumption.

    (* b === BTrue *)
    simpl in H5.
    apply negb_false_iff in H5.
    apply E_IfTrue.
    (* if *)   assumption.
    (* then *) assumption.
Qed.
(* ☐ *)


Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.
Proof.
  intros b c Hb. split; intros H.
  Case "->".
    inversion H; subst.
    SCase "E_WhileEnd".
      apply E_Skip.
    SCase "E_WhileLoop".
      rewrite Hb in H2. inversion H2.
  Case "<-".
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity. Qed.

(* 練習問題: ★★ (WHILE_false_informal) *)
(*
WHILE_falseの非形式的証明を記述しなさい。
 *)
(*
「定理」: もしbがBFalseと同値ならば WHILE b DO c END は SKIP と同値である。

「証明」:
  - (->) すべての st と st' に対して、もし WHILE b DO c END / st || st' ならば SKIP / st || st' となることを示す。
    WHILE b DO c END / st || st' を示すのに使うことができた可能性のある規則、つまり E_WhileEnd と W_WhileLoop で、場合分けをする。
    - WHILE b DO c END / st || st' の導出の最後の規則が E_WhileEnd であると仮定する。このとき、 E_WhileEnd の仮定より st = st' となる。したがって SKIP / st || st を示せばよい。これは E_Skip の導出規則により成り立つ。
    - WHILE b DO c END / st || st' の導出の最後の規則が E_WhileLoop であると仮定する。このとき E_WhileLoop の仮定より beval st b = true となる。bがBFalseと同値である仮定から、任意の st について beval st b = beval st BFalse である。よって beval st BFalse = true となるが、これは矛盾である。したがって最後の規則は E_WhileLoop ではありえない。

  - (<-) すべての st と st' について、もし SKIP / st || st' ならば WHILE b DO c END / st || st' となることを示す。
    - SKIP / st || st' から st = st'。
      また、 b と BFalse が同値であることから、E_WhileEnd が適用でき、 WHILE b DO c END / st || st となる。
      したがって WHILE b DO c END / st || st'
 *)
(* ☐ *)
