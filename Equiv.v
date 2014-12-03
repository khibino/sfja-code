
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
 b が真に解釈されるとき、 (WHILE b DO c END) は、最終状態に到達しない。
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

(** 同値である2つのプログラムとその同値の証明の例です... *)

Example congruence_example:
  cequiv
    (X ::= ANum 0;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (X ::= ANum 0;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X)   (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
    apply refl_cequiv.
    apply CIf_congruence.
      apply refl_bequiv.
      apply CAss_congruence. unfold aequiv. simpl.
        symmetry. apply minus_diag.
      apply refl_cequiv.
Qed.

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

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | i ::= a  =>
      CAss i (fold_constants_aexp a)
  | c1 ; c2  =>
      (fold_constants_com c1) ; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (X ::= APlus (ANum 4) (ANum 5);
     Y ::= AMinus (AId X) (ANum 3);
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END) =
  (X ::= ANum 9;
   Y ::= AMinus (AId X) (ANum 3);
   IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
     SKIP
   ELSE
     (Y ::= ANum 0)
   FI;
   Y ::= ANum 0;
   WHILE BEq (AId Y) (ANum 0) DO
     X ::= APlus (AId X) (ANum 1)
   END).
Proof. reflexivity. Qed.

(** ** 定数畳み込みの健全性 *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  aexp_cases (induction a) Case; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (APlus a1 a2)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(* 練習問題: ★★★, optional (fold_bexp_BEq_informal) *)

(*
ここに、ブール式の定数畳み込みに関する健全性の議論のBEqの場合の非形
式的証明を示します。これを丁寧に読みその後の形式的証明と比較しなさい
。次に、形式的証明のBLe部分を(もし可能ならばBEqの場合を見ないで)記述
しなさい。

「定理」:ブール式に対する定数畳み込み関数fold_constants_bexpは健全で
ある。

「証明」:すべてのブール式bについてbがfold_constants_bexp と同値であ
ることを示す。 bについての帰納法を行う。 bがBEq a1 a2という形の場合
を示す。

この場合、
       beval st (BEq a1 a2)
     = beval st (fold_constants_bexp (BEq a1 a2)).

を示せば良い。これには2種類の場合がある:

  * 最初に、あるn1とn2について、fold_constants_aexp a1 = ANum n1かつ
    fold_constants_aexp a2 = ANum n2と仮定する。

    この場合、
               fold_constants_bexp (BEq a1 a2)
             = if beq_nat n1 n2 then BTrue else BFalse

    かつ
               beval st (BEq a1 a2)
             = beq_nat (aeval st a1) (aeval st a2).

    となる。算術式についての定数畳み込みの健全性(補題
    fold_constants_aexp_sound)より、
               aeval st a1
             = aeval st (fold_constants_aexp a1)
             = aeval st (ANum n1)
             = n1

    かつ
               aeval st a2
             = aeval st (fold_constants_aexp a2)
             = aeval st (ANum n2)
             = n2,

    である。従って、
               beval st (BEq a1 a2)
             = beq_nat (aeval a1) (aeval a2)
             = beq_nat n1 n2.

    となる。また、(n1 = n2とn1 <> n2の場合をそれぞれ考えると)
               beval st (if beq_nat n1 n2 then BTrue else BFalse)
             = if beq_nat n1 n2 then beval st BTrue else beval st
    BFalse
             = if beq_nat n1 n2 then true else false
             = beq_nat n1 n2.

    となることは明らかである。ゆえに
               beval st (BEq a1 a2)
             = beq_nat n1 n2.
             = beval st (if beq_nat n1 n2 then BTrue else BFalse),

    となる。これは求められる性質である。

  * それ以外の場合、fold_constants_aexp a1とfold_constants_aexp a2
    のどちらかは定数ではない。この場合、
               beval st (BEq a1 a2)
             = beval st (BEq (fold_constants_aexp a1)
                             (fold_constants_aexp a2)),

    を示せば良い。 bevalの定義から、これは
               beq_nat (aeval st a1) (aeval st a2)
             = beq_nat (aeval st (fold_constants_aexp a1))
                       (aeval st (fold_constants_aexp a2)).

    を示すことと同じである。算術式についての定数畳み込みの健全性(
    fold_constants_aexp_sound)より、
             aeval st a1 = aeval st (fold_constants_aexp a1)
             aeval st a2 = aeval st (fold_constants_aexp a2),

    となり、この場合も成立する。
 *)
(* ☐ *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  bexp_cases (induction b) Case;

    try reflexivity.
  Case "BEq".
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1'.
    remember (fold_constants_aexp a2) as a2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity
).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity
).
    destruct a1'; destruct a2'; try reflexivity.
      simpl. destruct (beq_nat n n0); reflexivity.

  Case "BLe".
    simpl.
    remember (fold_constants_aexp a) as a'.
    remember (fold_constants_aexp a0) as a0'.
    replace (aeval st a) with (aeval st a').
    replace (aeval st a0) with (aeval st a0').
    destruct a'; destruct a0'
    ; try reflexivity.
    simpl. destruct (ble_nat n n0); reflexivity.

    subst a0'. rewrite <- fold_constants_aexp_sound. reflexivity.
    subst a'. rewrite <- fold_constants_aexp_sound. reflexivity.

  Case "BNot".
    simpl. remember (fold_constants_bexp b) as b'.
    rewrite IHb.
    destruct b'; reflexivity.
  Case "BAnd".
    simpl.
    remember (fold_constants_bexp b1) as b1'.
    remember (fold_constants_bexp b2) as b2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity. Qed.
(* ☐ *)

(** **** 練習問題: ★★★ (fold_constants_com_sound) *)
(** 次の証明の[WHILE]の場合を完成させなさい。*)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";". apply CSeq_congruence; assumption.
  Case "IFB".
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      try (apply CWhile_congruence; assumption).
    SCase "b is true".
      apply WHILE_true. assumption.
    SCase "b is false".
      apply WHILE_false. assumption.
Qed.
(** [] *)

(** *** (0 + n)の消去の健全性、再び *)

(** **** 練習問題: ★★★★, optional (optimize_0plus) *)
(** Imp_J.vの[optimize_0plus]の定義をふり返ります。
[[
    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.
]]
   この関数は、[aexp]の上で定義されていて、状態を扱わないことに注意します。

   変数を扱えるようにした、この関数の新しいバージョンを記述しなさい。
   また、[bexp]およびコマンドに対しても、同様のものを記述しなさい:
[[
     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com
]]
   これらの関数の健全性を、[fold_constants_*]について行ったのと同様に証明しなさい。
   [optimize_0plus_com]の証明においては、合同性補題を確実に使いなさい
   (そうしなければ証明はとても長くなるでしょう!)。

   次に、コマンドに対して次の処理を行う最適化関数を定義しなさい。行うべき処理は、
   まず定数畳み込みを([fold_constants_com]を使って)行い、
   次に[0 + n]項を([optimize_0plus_com]を使って)消去することです。

   - この最適化関数の出力の意味のある例を示しなさい。

   - この最適化関数が健全であることを示しなさい。(この部分は「とても」簡単なはずです。) *)

Fixpoint optimize_0plus_aexp (e:aexp) : aexp :=
  match e with
    | ANum n =>
      ANum n
    | AId X => AId X
    | APlus (ANum 0) e2 =>
      optimize_0plus_aexp e2
    | APlus e1 e2 =>
      APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
    | AMinus e1 e2 =>
      AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
    | AMult e1 e2 =>
      AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  end.

Fixpoint optimize_0plus_bexp (e:bexp) : bexp :=
  match e with
    | BEq a1 a2 => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BLe a1 a2 => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | b => b
  end.

Fixpoint optimize_0plus_com (c:com) : com :=
  match c with
    | CSkip => CSkip
    | CAss id ae => CAss id (optimize_0plus_aexp ae)
    | CSeq c1 c2 => CSeq (optimize_0plus_com c1) (optimize_0plus_com c2)
    | CIf b c1 c2 => CIf (optimize_0plus_bexp b)
                         (optimize_0plus_com c1)
                         (optimize_0plus_com c2)
    | CWhile b c => CWhile (optimize_0plus_bexp b) (optimize_0plus_com c)
  end.

Theorem optimize_0plus_aexp_sound :
  atrans_sound optimize_0plus_aexp.
Proof.
  intros a st.
  aexp_cases (induction a as [ | | a1 | | ]) Case; simpl

  ; [ reflexivity (* num *)
    | reflexivity (* id *)
    | destruct a1 as [ [ | ] | | | | ] eqn: a1H  (* plus *)
    | (* minus *)
    | (* mult *)
    ]
  ; rewrite IHa1; rewrite IHa2; reflexivity.
Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  intros b. unfold bequiv. intros st.

  bexp_cases (induction b) Case
  ; try reflexivity

  ; rename a into a1; rename a0 into a2; simpl
  ; remember (optimize_0plus_aexp a1) as a1'
  ; remember (optimize_0plus_aexp a2) as a2'
  ; replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- optimize_0plus_aexp_sound; reflexivity)
  ; replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- optimize_0plus_aexp_sound; reflexivity)
  ; reflexivity.
Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  intro c.

  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply optimize_0plus_aexp_sound.
  Case ";". apply CSeq_congruence; assumption.
  Case "IFB".
    assert (bequiv b (optimize_0plus_bexp b)).
      SCase "Pf of assertion". apply optimize_0plus_bexp_sound.
    remember (optimize_0plus_bexp b) as b'.
    destruct b';
      apply CIf_congruence; assumption.
  Case "WHILE".
    assert (bequiv b (optimize_0plus_bexp b)).
      SCase "Pf of assertion". apply optimize_0plus_bexp_sound.
    remember (optimize_0plus_bexp b) as b'.
    destruct b';
      apply CWhile_congruence; assumption.
Qed.
(** [] *)


(* プログラムが同値でないことを証明する *)

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i' => if beq_id i i' then u else AId i'
  | APlus a1 a2 => APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 => AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 => AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53)) (APlus (AId Y) (AId X)) =
  (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity. Qed.

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1; i2 ::= a2)
         (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  remember (X ::= APlus (AId X) (ANum 1);
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  remember (update (update empty_state X 1) Y 1) as st1.
  remember (update (update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state || st1);
  assert (H2: c2 / empty_state || st2);
  try (subst;
       apply E_Seq with (st' := (update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.

(** **** 練習問題: ★★★★ (better_subst_equiv) *)
(** 上で成立すると考えていた同値は、完全に意味がないものではありません。
    それは実際、ほとんど正しいのです。それを直すためには、
    最初の代入の右辺に変数[X]が現れる場合を排除すれば良いのです。*)

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (update st i ni) a = aeval st a.
Proof.
  intros i st a ni NU.
  induction NU; subst
  ; try (simpl;
         rewrite -> IHNU1;
         rewrite -> IHNU2;
         reflexivity).
  (* Num *)
    reflexivity.
  (* Id *)
    simpl. unfold update.
    SearchAbout beq_id.
    apply not_eq_beq_id_false in H.
    rewrite -> H. reflexivity.
Qed.

(** [var_not_used_in_aexp]を使って、[subst_equiv_property]の正しいバージョンを形式化し、
    証明しなさい。*)
Definition better_subst_equiv_property :=
  forall i1 i2 a1 a2,
    var_not_used_in_aexp i1 a1 ->
    cequiv (i1 ::= a1; i2 ::= a2)
           (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

Theorem better_subst_equiv : better_subst_equiv_property.
Proof.
  intros i1 i2 a1 a2 NU.

  split; intro H  (* <-> ==> <- & ->  ==> = & = *)
  ; inversion H; subst  (* generate st'0 *)
  ; (apply E_Seq with (st' := st'0)
     ; [ assumption
       | inversion H5; subst ])
  ; (apply E_Ass; inversion H2; subst)
  ; [ | symmetry ] (* from <- into -> *)

  ; (aexp_cases (induction a2 as [ | i | | | ] ) Case; simpl

     ; [ reflexivity (* num *)
       | destruct (beq_id i1 i) as [] eqn: EQ
         ; [ unfold update; rewrite EQ
             ; inversion NU; subst
             ; apply aeval_weakening; assumption
           | reflexivity]
         (* id *)

       | (* plus *) | (* minus *) | (* mult *) ]

     ; (rewrite IHa2_1
        ; [ rewrite IHa2_2
            ; [ reflexivity
              | apply E_Seq with (st' := update st i1 (aeval st a1))
              | ]
            ; apply E_Ass; reflexivity
          | apply E_Seq with (st' := update st i1 (aeval st a1))
          | ]
        ; apply E_Ass; reflexivity) ).
Qed.
(** [] *)

(** **** 練習問題: ★★★, recommended (inequiv_exercise) *)
Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  intro eqv.
  remember (eqv empty_state empty_state) as eqH.
  destruct eqH as [ LH RH ].
  apply (WHILE_true_nonterm BTrue SKIP empty_state empty_state).
    intro st. reflexivity.
    exact (RH (E_Skip empty_state)).
Qed.
(** [] *)

(** * 外延性を使わずに行う (Optional) *)

Definition stequiv (st1 st2 : state) : Prop :=
  forall (X:id), st1 X = st2 X.

Notation "st1 '~' st2" := (stequiv st1 st2) (at level 30).

(** [stequiv]が同値関係(_equivalence_、 つまり、反射的、対称的、推移的関係)
    であることを証明することは容易です。この同値関係により、
    すべての状態の集合は同値類に分割されます。*)

(** **** 練習問題: ★, optional (stequiv_refl) *)
Lemma stequiv_refl : forall (st : state),
  st ~ st.
Proof.
  intros st i. reflexivity.
Qed.
(** [] *)

(** **** 練習問題: ★, optional (stequiv_sym) *)
Lemma stequiv_sym : forall (st1 st2 : state),
  st1 ~ st2 ->
  st2 ~ st1.
Proof.
  intros st1 st2 H i.
  symmetry. exact (H i).
Qed.
(** [] *)

(** **** 練習問題: ★, optional (stequiv_trans) *)
Lemma stequiv_trans : forall (st1 st2 st3 : state),
  st1 ~ st2 ->
  st2 ~ st3 ->
  st1 ~ st3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 star, optional (stequiv_update) *)
(** **** 練習問題: ★, optional (stequiv_update) *)
Lemma stequiv_update : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (X:id) (n:nat),
  update st1 X n ~ update st2 X n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* It is then straightforward to show that [aeval] and [beval] behave
    uniformly on all members of an equivalence class: *)
(** [aeval]と[beval]が同値類のすべての要素に対して同じように振る舞うことは、
    ここからストレートに証明できます: *)

(* **** Exercise: 2 stars, optional (stequiv_aeval) *)
(** **** 練習問題: ★★, optional (stequiv_aeval) *)
Lemma stequiv_aeval : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (a:aexp), aeval st1 a = aeval st2 a.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (stequiv_beval) *)
(** **** 練習問題: ★★, optional (stequiv_beval) *)
Lemma stequiv_beval : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (b:bexp), beval st1 b = beval st2 b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma stequiv_ceval: forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (c: com) (st1': state),
    (c / st1 || st1') ->
    exists st2' : state,
    ((c / st2 || st2') /\  st1' ~ st2').
Proof.
  intros st1 st2 STEQV c st1' CEV1. generalize dependent st2.
  induction CEV1; intros st2 STEQV.
  Case "SKIP".
    exists st2. split.
      constructor.
      assumption.
  Case ":=".
    exists (update st2 l n). split.
       constructor.  rewrite <- H. symmetry.  apply stequiv_aeval.
       assumption. apply stequiv_update.  assumption.
  Case ";".
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
    exists st2''.  split.
      apply E_Seq with st2';  assumption.
      assumption.
  Case "IfTrue".
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
    exists st2'.  split.
      apply E_IfTrue.  rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption. assumption.
  Case "IfFalse".
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
    exists st2'. split.
     apply E_IfFalse. rewrite <- H. symmetry. apply stequiv_beval.
     assumption.  assumption. assumption.
  Case "WhileEnd".
    exists st2. split.
      apply E_WhileEnd. rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption.
  Case "WhileLoop".
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
    exists st2''. split.
      apply E_WhileLoop with st2'.  rewrite <- H. symmetry.
      apply stequiv_beval. assumption. assumption. assumption.
      assumption.
Qed.

Reserved Notation "c1 '/' st '||'' st'" (at level 40, st at level 39).

Inductive ceval' : com -> state -> state -> Prop :=
  | E_equiv : forall c st st' st'',
    c / st || st' ->
    st' ~ st'' ->
    c / st ||' st''
  where   "c1 '/' st '||'' st'" := (ceval' c1 st st').

Definition cequiv' (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st ||' st') <-> (c2 / st ||' st').

Lemma cequiv__cequiv' : forall (c1 c2: com),
  cequiv c1 c2 -> cequiv' c1 c2.
Proof.
  unfold cequiv, cequiv'; split; intros.
    inversion H0 ; subst.  apply E_equiv with st'0.
    apply (H st st'0); assumption. assumption.
    inversion H0 ; subst.  apply E_equiv with st'0.
    apply (H st st'0). assumption. assumption.
Qed.

(** **** 練習問題: ★★, optional (identity_assignment') *)
(** 最後にもとの例を再度扱います... (証明を完成しなさい。) *)

Example identity_assignment' :
  cequiv' SKIP (X ::= AId X).
Proof.
    unfold cequiv'.  intros.  split; intros.
    Case "->".
      inversion H; subst; clear H. inversion H0; subst.
      apply E_equiv with (update st'0 X (st'0 X)).
      constructor. reflexivity.  apply stequiv_trans with st'0.
      unfold stequiv. intros. apply update_same.
      reflexivity. assumption.
    Case "<-".
      (* FILL IN HERE *) Admitted.
(** [] *)

(** * さらなる練習問題 *)

(** **** 練習問題: ★★★★, optional (for_while_equiv) *)
(** この練習問題は、Imp_J.vのoptionalの練習問題 add_for_loop を拡張したものです。
    もとの add_for_loop は、コマンド言語に C-言語のスタイルの [for]ループを
    拡張しなさい、というものでした。
    ここでは次のことを証明しなさい:
[[
      for (c1 ; b ; c2) {
          c3
      }
]]
    は
[[
       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
]]
    と同値である。
*)
(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★★, optional (swap_noninterfering_assignments) *)
Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1; l2 ::= a2)
    (l2 ::= a2; l1 ::= a1).
Proof.
(* Hint: You'll need [functional_extensionality] *)
(* ヒント: [functional_extensionality]を必要とするでしょう。 *)
(* FILL IN HERE *) Admitted.
(** [] *)
