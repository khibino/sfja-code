
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

Lemma WHILE_true_nonterm :
  forall b c st st',
    bequiv b BTrue ->
    ~( (WHILE b DO c END) / st || st').
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  ceval_cases (induction H) Case;

    inversion Heqcw; subst; clear Heqcw.
  Case "E_WhileEnd".    rewrite Hb in H. inversion H.
  Case "E_WhileLoop".   apply IHceval2. reflexivity. Qed.


(* 練習問題: ★★, optional (WHILE_true_nonterm_informal) *)

(* 補題WHILE_true_nontermが意味するものを日本語で書きなさい。 *)

(*
 b が真に解釈されるとき、 (WHILE b DO c END) は、あらゆる状態を遷移しえない。
 *)

(* ☐ *)

(* 練習問題: ★★, recommended (WHILE_true) *)

(*
ここでWHILE_true_nontermを使いなさい。
 *)

Theorem WHILE_true: forall b c,
     bequiv b BTrue ->
     cequiv
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  intros b c Hb.
  split.
    (* -> *)
    intros H.
    apply WHILE_true_nonterm in H.
    inversion H. apply Hb.

    (* <- *)
    intros H.
    apply WHILE_true_nonterm in H.
    inversion H. intros st''. reflexivity.
Qed.
(* ☐ *)

Theorem loop_unrolling:
  forall b c, cequiv
            (WHILE b DO c END)
            (IFB b THEN (c; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    SCase "loop doesn't run".
      apply E_IfFalse. assumption. apply E_Skip.
    SCase "loop runs".
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  Case "<-".
    inversion Hce; subst.
    SCase "loop runs".
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    SCase "loop doesn't run".
      inversion H5; subst. apply E_WhileEnd. assumption. Qed.

(* 練習問題: ★★, optional (seq_assoc) *)

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;c2);c3) (c1;(c2;c3)).
Proof.
  intros c1 c2 c3. split; intros Hce.

  (* -> *)
    inversion Hce; subst.
    inversion H1;  subst.
    apply E_Seq with (st' := st'1).
    assumption.
    apply E_Seq with (st' := st'0).
    assumption. assumption.

  (* <- *)
    inversion Hce; subst.
    inversion H4; subst.
    apply E_Seq with (st' := st'1).
    apply E_Seq with (st' := st'0).
    assumption. assumption. assumption.
Qed.
(* ☐ *)

Theorem identity_assignment_first_try :
  forall (X:id),
    cequiv
      (X ::= AId X)
      SKIP.
Proof.
  intros. split; intro H.
  Case "->".
  inversion H; subst. simpl.
  replace (update st X (st X)) with st.
  constructor.
Admitted.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) -> f = g.

Theorem identity_assignment :
  forall (X:id),
    cequiv
      (X ::= AId X)
      SKIP.
Proof.
  intros. split; intro H.
    Case "->".
      inversion H; subst. simpl.
      replace (update st X (st X)) with st.
      constructor.
      apply functional_extensionality. intro.
      rewrite update_same; reflexivity.
    Case "<-".
      inversion H; subst.
      assert (st' = (update st' X (st' X))).
         apply functional_extensionality. intro.
         rewrite update_same; reflexivity.
      rewrite H0 at 2.
      constructor. reflexivity.
Qed.

(* 練習問題: ★★, recommended (assign_aequiv) *)

Theorem assign_aequiv :
  forall X e,
    aequiv (AId X) e ->
    cequiv SKIP (X ::= e).
Proof.
  intros X e aH.
  (* unfold aequiv in eqH. *)
  split; intro cH.

  (* -> *)
  inversion cH; subst.
  assert (st' = (update st' X (st' X))).
    apply functional_extensionality. intro.
    rewrite update_same; reflexivity.
  rewrite -> H at 2.
  constructor.
  rewrite <- (aH st'). reflexivity.

  (* <- *)
  inversion cH; subst.
  rewrite <- (aH st). simpl.
  replace (update st X (st X)) with st.
  constructor.
  apply functional_extensionality. intro.
  rewrite update_same. reflexivity. reflexivity.
Qed.
(* ☐ *)


(* 振る舞い同値の性質 *)

(* 振る舞い同値は同値関係である *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity. Qed.

Lemma sym_aequiv :
  forall (a1 a2 : aexp),
    aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H. Qed.

Lemma trans_aequiv :
  forall (a1 a2 a3 : aexp),
    aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl. Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st || st' <-> c2 / st || st') as H'.
    SCase "Proof of assertion". apply H.
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A. Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st || st'). apply H12. apply H23. Qed.

(* 振る舞い同値は合同関係である *)

Theorem CAss_congruence :
  forall i a1 a1',
    aequiv a1 a1' ->
    cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  Case "->".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  Case "<-".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity. Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  Case "->".
    remember (WHILE b1 DO c1 END) as cwhile.
    induction Hce; inversion Heqcwhile; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite <- Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st'). apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
  Case "<-".
    remember (WHILE b1' DO c1' END) as c'while.
    induction Hce; inversion Heqc'while; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite -> Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st'). apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity. Qed.

(* **** Exercise: 3 stars, optional (CSeq_congruence) *)
(** **** 練習問題: ★★★, optional (CSeq_congruence) *)
Theorem CSeq_congruence_0 :
  forall c1 c1' c2 c2',
    cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (c1;c2) (c1';c2').
Proof.
  intros c1 c1' c2 c2' Hc1e Hc2e st st'.

  split; intro Hc.
  Case "->".
    inversion Hc; subst.
    Check (Hc1e st st'0).
    apply E_Seq with (st' := st'0).
    rewrite <- (Hc1e st st'0). assumption.
    rewrite <- (Hc2e st'0 st'). assumption.
  Case "<-".
    inversion Hc; subst.
    apply E_Seq with (st' := st'0).
    rewrite -> (Hc1e st st'0). assumption.
    rewrite -> (Hc2e st'0 st'). assumption.
Qed.

Theorem CSeq_congruence :
  forall c1 c1' c2 c2',
    cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (c1;c2) (c1';c2').
Proof.
  intros c1 c1' c2 c2' Hc1e Hc2e st st'.

  split; intro Hc
  ; inversion Hc; subst
  ; apply E_Seq with (st' := st'0)
  ; [ rewrite <- (Hc1e st st'0) | rewrite <- (Hc2e st'0 st') |
      rewrite -> (Hc1e st st'0) | rewrite -> (Hc2e st'0 st') ] ; assumption.
Qed.
(** [] *)

(* **** Exercise: 3 stars (CIf_congruence) *)
(** **** 練習問題: ★★★ (CIf_congruence) *)
Theorem CIf_congruence_0 :
  forall b b' c1 c1' c2 c2',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros b b' c1 c1' c2 c2' Hbe Hc1e Hc2e st st'.
  split; intro Hc.

  Case "->".
    inversion Hc; subst.

    SCase "true".
    apply E_IfTrue.
    Check (Hbe st).
    rewrite <- (Hbe st). assumption.
    rewrite <- (Hc1e st). assumption.

    SCase "false".
    apply E_IfFalse.
    rewrite <- (Hbe st). assumption.
    rewrite <- (Hc2e st). assumption.

  Case "<-".
    inversion Hc; subst.

    SCase "true".
    apply E_IfTrue.
    Check (Hbe st).
    rewrite -> (Hbe st). assumption.
    rewrite -> (Hc1e st). assumption.

    SCase "false".
    apply E_IfFalse.
    rewrite -> (Hbe st). assumption.
    rewrite -> (Hc2e st). assumption.
Qed.

Theorem CIf_congruence :
  forall b b' c1 c1' c2 c2',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros b b' c1 c1' c2 c2' Hbe Hc1e Hc2e st st'.

  split; intro Hc
  ; inversion Hc; subst
  ; [ apply E_IfTrue | apply E_IfFalse |
      apply E_IfTrue | apply E_IfFalse ]
  ; [ rewrite <- (Hbe st) | rewrite <- (Hc1e st) |
      rewrite <- (Hbe st) | rewrite <- (Hc2e st) |
      rewrite -> (Hbe st) | rewrite -> (Hc1e st) |
      rewrite -> (Hbe st) | rewrite -> (Hc2e st) ]
  ; assumption.
Qed.
(** [] *)


(* ケーススタディ: 定数畳み込み *)

(* プログラム変換の健全性 *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* 定数畳み込み変換 *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
    | ANum n => ANum n
    | AId i => AId i
    | APlus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) => ANum (n1 + n2)
        | (a1', a2') => APlus a1' a2'
      end
    | AMinus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) => ANum (n1 - n2)
        | (a1', a2') => AMinus a1' a2'
      end
    | AMult a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) => ANum (n1 * n2)
        | (a1', a2') => AMult a1' a2'
      end
  end.

Example fold_aexp_ex1 :
  fold_constants_aexp
    (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp
    (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else
                                  BFalse
        | (a1', a2') => BEq a1' a2'
      end
    | BLe a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) => if ble_nat n1 n2 then BTrue else
                                  BFalse
        | (a1', a2') => BLe a1' a2'
      end
    | BNot b1 =>
      match (fold_constants_bexp b1) with
        | BTrue => BFalse
        | BFalse => BTrue
        | b1' => BNot b1'
      end
    | BAnd b1 b2 =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
        | (BTrue, BTrue) => BTrue
        | (BTrue, BFalse) => BFalse
        | (BFalse, BTrue) => BFalse
        | (BFalse, BFalse) => BFalse
        | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
    fold_constants_bexp
      (BAnd (BEq (AId X) (AId Y))
            (BEq (ANum 0)
                 (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.
