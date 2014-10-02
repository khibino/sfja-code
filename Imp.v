
(* 単純な命令型プログラム *)

Require Export SfLib.

(* 算術式とブール式 *)

(* 構文 *)

Module AExp.

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


(* 評価 *)

Fixpoint aeval (e : aexp) : nat :=
  match e with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.


(* 最適化(Optimization) *)

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

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.


Theorem optimize_0plus_sound:
  forall e, aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
    SCase "e1 = ANum n". destruct n.
      SSCase "n = 0". simpl. apply IHe2.
      SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
    SCase "e1 = APlus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMinus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity. Qed.


(* Coq の自動化 *)

(* タクティカル(Tacticals) *)

(* tryタクティカル *)

(* ;タクティカル *)

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
Qed.

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n;

  simpl;

  reflexivity.
Qed.

Theorem optimize_0plus_sound':
  forall e, aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;

    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
  Case "ANum". reflexivity.
  Case "APlus".
    destruct e1;

      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity
).
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity. Qed.

Theorem optimize_0plus_sound'':
  forall e, aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;

    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);

    try reflexivity.
  Case "APlus".
    destruct e1; try (simpl; simpl in IHe1; rewrite IHe1;
                      rewrite IHe2; reflexivity).
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity. Qed.


(* 新しいタクティック記法を定義する *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.


(* 場合分けを万全にする *)

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Theorem optimize_0plus_sound''':
  forall e, aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  aexp_cases (induction e) Case;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.

  Case "APlus".
    aexp_cases (destruct e1) SCase;
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity
).
    SCase "ANum". destruct n;
      simpl; rewrite IHe2; reflexivity. Qed.

(* 練習問題: ★★★ (optimize_0plus_b) *)

(*
optimize_0plusの変換がaexpの値を変えないことから、 bexpの値を変えずに、
bexpに現れるaexpをすべて変換するために optimize_0plusが適用できるべきで
しょう。 bexpについてこの変換をする関数を記述しなさい。そして、それが健
全であることを証明しなさい。ここまで見てきたタクティカルを使って証明を可
能な限りエレガントにしなさい。
 *)

Fixpoint optimize_0plus_b (e:bexp) : bexp :=
  match e with
    | BEq a1 a2  => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2  => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1    => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    | e          => e
  end.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse"
  | Case_aux c "BEq"   | Case_aux c "BLe"
  | Case_aux c "BNot"  | Case_aux c "BAnd"
  ].

Theorem optimize_0plus_b_sound:
  forall e, beval (optimize_0plus_b e) = beval e.
Proof.
  bexp_cases (induction e
               as [ | | a0 a1 | a0 a1 | b IHb | b0 IHb0 b1 IHb1 ])
             Case
  ; simpl
  ; try (rewrite -> (optimize_0plus_sound a0) ;
         rewrite -> (optimize_0plus_sound a1) )
  ; [ | | | | rewrite -> IHb | rewrite -> IHb0 ; rewrite IHb1 ]
  ; reflexivity.
Qed.
  (*
  induction e.
  (* BTrue  *) simpl. reflexivity.
  (* BFalse *) simpl. reflexivity.
  (* BEq *)
    simpl.
    rewrite -> (optimize_0plus_sound a).
    rewrite -> (optimize_0plus_sound a0).
    reflexivity.
  (* BLe *)
    simpl.
    rewrite -> (optimize_0plus_sound a).
    rewrite -> (optimize_0plus_sound a0).
    reflexivity.
  (* BNot *) simpl. rewrite -> IHe. reflexivity.
  (* BAnd *) simpl. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
   *)

(* ☐ *)

(* 練習問題: ★★★★, optional (optimizer) *)

(*
設計練習: 定義したoptimize_0plus関数で実装された最適化は、算術式やブール
式に対して考えられるいろいろな最適化の単なる1つに過ぎません。より洗練さ
れた最適化関数を記述し、その正しさを証明しなさい。
 *)

(* ☐ *)

Example silly_presburger_example :
  forall m n o p,
    m + n <= n + o /\ o + 3 = p + 3 ->
    m <= p.
Proof.
  intros. omega.
Qed.

(* 便利なタクティックをさらにいくつか *)


(* 関係としての評価 *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n: nat), aevalR (ANum n) n
| E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
              aevalR e1 n1 ->
              aevalR e2 n2 ->
              aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
              aevalR e1 n1 ->
              aevalR e2 n2 ->
              aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
              aevalR e1 n1 ->
              aevalR e2 n2 ->
              aevalR (AMult e1 e2) (n1 * n2).

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.


Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].


Theorem aeval_iff_aevalR :
  forall a n, (a || n) <-> aeval a = n.
Proof.
 split.
 Case "->".
   intros H.
   aevalR_cases (induction H) SCase; simpl.
   SCase "E_ANum".
     reflexivity.
   SCase "E_APlus".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase;
      simpl; intros; subst.
   SCase "ANum".
     apply E_ANum.
   SCase "APlus".
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMinus".
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.


Theorem aeval_iff_aevalR' :
  forall a n, (a || n) <-> aeval a = n.
Proof.
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* 練習問題: ★★, optional (bevalR) *)

(*
関係bevalRをaevalRと同じスタイルで記述し、それがbevalと同値であることを
証明しなさい。
 *)

(* 推論規則記法 *)

End AExp.


(* 変数を持つ式 *)

(* 識別子 *)

Module Id.

Inductive id : Type :=
  Id : nat -> id.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl :
  forall X, true = beq_id X X.
Proof.
  intros. destruct X.
  apply beq_nat_refl. Qed.

(* 練習問題: ★, optional (beq_id_eq) *)

(*
この問題とそれに続く練習問題では、帰納法を使わずに、既に証明した自然数の
同様の結果を適用しなさい。上述したいくつかのタクティックが使えるかもしれ
ません。
 *)

Theorem beq_id_eq :
  forall i1 i2, true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2 EQ.
  destruct i1 as [n1].
  destruct i2 as [n2].
  unfold beq_id in EQ.
  apply beq_nat_eq in EQ.
  rewrite <- EQ.
  reflexivity.
Qed.
(* ☐ *)

(* 練習問題: ★, optional (beq_id_false_not_eq) *)

Theorem beq_id_false_not_eq :
  forall i1 i2, beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 NE.
  destruct i1 as [n1].
  destruct i2 as [n2].
  unfold beq_id in NE.
  apply beq_nat_false in NE.
  intro eq.
  apply NE.
  inversion eq as [ID]. (* 自己再帰していないので有り? *)
  reflexivity.
Qed.
(* ☐ *)

(* 練習問題: ★, optional (not_eq_beq_id_false) *)

Theorem not_eq_beq_id_false :
  forall i1 i2, i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros i1 i2 NE.
  destruct i1 as [n1].
  destruct i2 as [n2].
  unfold beq_id.
  apply not_eq_beq_false.
  intros EQN.
  apply NE.
  rewrite <- EQN.
  reflexivity.
Qed.
(* ☐ *)

(* 練習問題: ★, optional (beq_id_sym) *)

Theorem beq_id_sym:
  forall i1 i2, beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros i1 i2.
  assert (forall a b, a = b -> beq_id a b = true).
    intros a b EQ.
    rewrite -> EQ.
    rewrite <- (beq_id_refl b).
    reflexivity.

  destruct (beq_id i1 i2) as [|] eqn: LE.

    destruct (beq_id i2 i1) as [|] eqn: RE.

    (* t t *) reflexivity.
    (* t f *)
      symmetry in LE.
      apply beq_id_eq in LE.
      rewrite <- LE in RE.
      rewrite <- beq_id_refl in RE.
      discriminate RE.

    destruct (beq_id i2 i1) as [|] eqn: RE.
    (* f t *)
      symmetry in RE.
      apply beq_id_eq in RE.
      rewrite RE in LE.
      rewrite <- beq_id_refl in LE.
      discriminate LE.

    (* f f *) reflexivity.
Qed.
(* ☐ *)

End Id.


(* 状態 *)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (X:id) (n : nat) : state :=
  fun X' => if beq_id X X' then n else st X'.


(* 練習問題: ★★, optional (update_eq) *)

Theorem update_eq :
  forall n X st, (update st X n) X = n.
Proof.
Admitted.
(* ☐ *)

(* 練習問題: ★★, optional (update_neq) *)

Theorem update_neq :
  forall V2 V1 n st,
    beq_id V2 V1 = false ->
    (update st V2 n) V1 = (st V1).
Proof.
Admitted.
(* ☐ *)

(* 練習問題: ★★, optional (update_example) *)

(*
タクティックを使って遊び始める前に、定理が言っていることを正確に理解している
ことを確認しなさい!
 *)

Theorem update_example :
  forall (n:nat), (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
Admitted.
(* ☐ *)

(* 練習問題: ★★ (update_shadow) *)

Theorem update_shadow :
  forall x1 x2 k1 k2 (f : state),
    (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
Admitted.
(* ☐ *)

(* 練習問題: ★★, optional (update_same) *)

Theorem update_same :
  forall x1 k1 k2 (f : state),
    f k1 = x1 ->
    (update f k1 x1) k2 = f k2.
Proof.
Admitted.
(* ☐ *)

(* 練習問題: ★★, optional (update_permute) *)

Theorem update_permute :
  forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false ->
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
Admitted.
(* ☐ *)

(* 構文 *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

(* 評価 *)


Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
    | ANum n => n
    | AId X => st X
    | APlus a1 a2 => (aeval st a1) + (aeval st a2)
    | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
    | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
    | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
    | BNot b1 => negb (beval st b1)
    | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* コマンド *)

(* 構文 *)

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
    | Case_aux c "IFB" | Case_aux c "WHILE" ].


Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).


Definition fact_in_coq : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* 例 *)


(* 割り当て: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;
  X ::= AMinus (AId X) (ANum 1).

(* ループ: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;
  Z ::= ANum 5 ;
  subtract_slowly.

(* 無限ループ: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* 階乗関数再び *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1 ;
  fact_loop.

(* 評価 *)

(* 評価関数 *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        update st l (aeval st a1)
    | c1 ; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st
  end.


Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          update st l (aeval st a1)
      | c1 ; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.


Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.


(* 練習問題: ★★, recommended (pup_to_n) *)

(*
1 から X までの整数を変数 Y に足す (つまり 1 + 2 + ... + X) Imp プログラムを
書きなさい。下に示したテストを満たすことを確認しなさい。
 *)

Definition pup_to_n : com :=
   admit.

(* ☐ *)

(* 練習問題: ★★, optional (peven) *)

(*
X が偶数だったら Z に 0 を、そうでなければ Z に 1 をセットする While プログラ
ムを書きなさい。テストには ceval_test を使いなさい。
 *)

(* ☐ *)


(* 関係としての評価 *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st || (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Example ceval_example1:
    (X ::= ANum 2;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity. Qed.


(* 練習問題: ★★ (ceval_example2) *)

Example ceval_example2:
    (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
Admitted.
(* ☐ *)

(* 関係による評価とステップ指数を利用した評価の等価性 *)

Theorem ceval_step__ceval:
  forall c st st',
    (exists i, ceval_step st c i = Some st') ->
    c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  Case "i = 0 -- contradictory".
    intros c st st' H. inversion H.

  Case "i = S i'".
    intros c st st' H.
    com_cases (destruct c) SCase;
           simpl in H; inversion H; subst; clear H.
      SCase "SKIP". apply E_Skip.
      SCase "::=". apply E_Ass. reflexivity.

      SCase ";".
        remember (ceval_step st c1 i') as r1. destruct r1.
        SSCase "Evaluation of r1 terminates normally".
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        SSCase "Otherwise -- contradiction".
          inversion H1.

      SCase "IFB".
        remember (beval st b) as r. destruct r.
        SSCase "r = true".
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        SSCase "r = false".
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      SCase "WHILE". remember (beval st b) as r. destruct r.
        SSCase "r = true".
          remember (ceval_step st c i') as r1. destruct r1.
          SSSCase "r1 = Some s".
            apply E_WhileLoop with s. rewrite Heqr. reflexivity.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
          SSSCase "r1 = None".
            inversion H1.
        SSCase "r = false".
          inversion H1.
          apply E_WhileEnd.
          rewrite Heqr. subst. reflexivity. Qed.


(* 練習問題: ★★★★ (ceval_step__ceval_inf) *)

(*
いつものテンプレートにのっとって、 ceval_step__ceval の形式的でない証明を書き
ましょう。 (帰納的に定義された値の場合分けに対するテンプレートは、帰納法の仮
定がないこと以外は帰納法と同じ見た目になるはずです。) 単に形式的な証明のステ
ップを書き写すだけでなく、人間の読者に主要な考えが伝わるようにしなさい。
 *)

(* ☐ *)

Theorem ceval_step_more:
  forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  Case "i1 = 0".
    inversion Hceval.
  Case "i1 = S i1'".
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    com_cases (destruct c) SCase.
    SCase "SKIP".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase "::=".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase ";".
      simpl in Hceval. simpl.
      remember (ceval_step st c1 i1') as st1'o.
      destruct st1'o.
      SSCase "st1'o = Some".
        symmetry in Heqst1'o.
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        inversion Hceval.

    SCase "IFB".
      simpl in Hceval. simpl.
      remember (beval st b) as bval.
      destruct bval; apply (IHi1' i2') in Hceval; assumption.

    SCase "WHILE".
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      remember (ceval_step st c i1') as st1'o.
      destruct st1'o.
      SSCase "st1'o = Some".
        symmetry in Heqst1'o.
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "i1'o = None".
        simpl in Hceval. inversion Hceval. Qed.

(* 練習問題: ★★★, recommended (ceval__ceval_step) *)

(*
以下の証明を完成させなさい。何度か ceval_step_more が必要となり、さらに <= と
plus に関するいくつかの基本的な事実が必要となるでしょう。
 *)

Theorem ceval__ceval_step:
  forall c st st',
    c / st || st' ->
    exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  ceval_cases (induction Hce) Case.
Admitted.
(* ☐ *)

Theorem ceval_and_ceval_step_coincide:
  forall c st st',
    c / st || st'
    <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.


(* 実行の決定性 *)

Theorem ceval_deterministic:
  forall c st st1 st2,
    c / st || st1 ->
    c / st || st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to true".
      reflexivity.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to false".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption. Qed.

Theorem ceval_deterministic' :
  forall c st st1 st2,
    c / st || st1 ->
    c / st || st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega. Qed.


(* プログラムの検証 *)

(* 基本的な例 *)

Theorem plus2_spec :
  forall st n st',
    st X = n ->
    plus2 / st || st' ->
    st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst.
  apply update_eq. Qed.

(* 練習問題: ★★★, recommended (XtimesYinZ_spec) *)

(*
XtimesYinZ の Imp プログラムの仕様を書いて証明しなさい。
 *)

(* ☐ *)

(* 練習問題: ★★★, recommended (loop_never_stops) *)

Theorem loop_never_stops :
  forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
Admitted.
(* ☐ *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ; c2 => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END => false
  end.


(* 練習問題: ★★, optional (no_whilesR) *)

(*
性質 no_whiles はプログラムが while ループを含まない場合 true を返します。
Inductive を使って c が while ループのないプログラムのとき証明可能な性質
no_whilesR を書きなさい。さらに、それが no_whiles と等価であることを示しなさ
い。
 *)

Inductive no_whilesR: com -> Prop :=

  .

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
Admitted.
(* ☐ *)

(* 練習問題: ★★★★, optional (no_whiles_terminating) *)

(*
while ループを含まない Imp プログラムは必ず停止します。これを定理として記述し
、証明しなさい。
(no_whiles と no_whilesR のどちらでも好きなほうを使いなさい。)
 *)

(* ☐ *)


(* プログラム正当性 (Optional) *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
    | O => 1
    | S n' => n * (real_fact n')
  end.


Definition fact_invariant (x:nat) (st:state) :=
  (st Y) * (real_fact (st Z)) = real_fact x.

Theorem fact_body_preserves_invariant:
  forall st st' x,
    fact_invariant x st ->
    st Z <> 0 ->
    fact_body / st || st' ->
    fact_invariant x st'.
Proof.
  unfold fact_invariant, fact_body.
  intros st st' x Hm HZnz He.
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold update. simpl.
  destruct (st Z) as [| z'].
    apply ex_falso_quodlibet. apply HZnz. reflexivity.
  rewrite <- Hm. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega.
  reflexivity. Qed.

Theorem fact_loop_preserves_invariant :
  forall st st' x,
    fact_invariant x st ->
    fact_loop / st || st' ->
    fact_invariant x st'.
Proof.
  intros st st' x H Hce.
  remember fact_loop as c.
  ceval_cases (induction Hce) Case;
              inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2.
      apply fact_body_preserves_invariant with st;
            try assumption.
      intros Contra. simpl in H0; subst.
      rewrite Contra in H0. inversion H0.
      reflexivity. Qed.

Theorem guard_false_after_loop:
  forall b c st st',
    (WHILE b DO c END) / st || st' ->
    beval st' b = false.
Proof.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  ceval_cases (induction Hce) Case;
     inversion Heqcloop; subst; clear Heqcloop.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2. reflexivity. Qed.

Theorem fact_com_correct :
  forall st st' x,
    st X = x ->
    fact_com / st || st' ->
    st' Y = real_fact x.
Proof.
  intros st st' x HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  rename st' into st''. simpl in H5.
  remember (update (update st Z (st X)) Y 1) as st'.
  assert (fact_invariant (st X) st').
    subst. unfold fact_invariant, update. simpl. omega.
  assert (fact_invariant (st X) st'').
    apply fact_loop_preserves_invariant with st'; assumption.
  unfold fact_invariant in H0.
  apply guard_false_after_loop in H5. simpl in H5.
  destruct (st'' Z).
  Case "st'' Z = 0". simpl in H0. omega.
  Case "st'' Z > 0 (impossible)". inversion H5.
Qed.

(* 練習問題: ★★★★, optional (subtract_slowly_spec) *)

(*
上の fact_com の仕様、および以下の不変式をガイドとして、 subtract_slowly の仕
様を証明しなさい。
 *)

Definition ss_invariant (x:nat) (z:nat) (st:state) :=
  minus (st Z) (st X) = minus z x.

(* ☐ *)

(* 追加の練習問題 *)

(* 練習問題: ★★★★, optional (add_for_loop) *)

(*
C 風の for ループをコマンドの言語に追加し、ceval の定義を for ループの意味も
与えるよう更新して、このファイルにあるすべての証明が Coq に通るよう、必要なと
ころへ for ループに対する場合分けを追加しなさい。

for ループは (a) 初めに実行される主張、 (b) 各繰り返しで実行される、ループを
続けてよいか決定するテスト、 (c) 各ループの繰り返しの最後に実行される主張、お
よび (d) ループの本体を構成する主張によってパラメタ化されていなければなりませ
ん。 (for ループに対する具体的な表記の構成を気にする必要はありませんが、やり
たければ自由にやって構いません。)
 *)

(* ☐ *)

(* 練習問題: ★★★, optional (short_circuit) *)

(*
多くのモダンなプログラミング言語はブール演算子 and に対し、「省略した」実行を
使っています。 BAnd b1 b2 を実行するには、まず b1 を評価します。それが false
に評価されるならば、b2 の評価はせず、すぐに BAnd 式全体の結果を false に評価
します。そうでなければ、BAnd 式の結果を決定するため、b2 が評価されます。

このように BAnd を省略して評価する、別のバージョンの beval を書き、それが
beavl と等価であることを証明しなさい。
 *)

(* 練習問題: ★★★★, recommended (stack_compiler) *)

(*
HP の電卓、Forth や Postscript などのプログラミング言語、および Java Virtual
Machine などの抽象機械はすべて、スタックを使って算術式を評価します。例えば、

   (2*3)+(3*(4-2))

という式は

   2 3 * 3 4 2 - * +

と入力され、以下のように実行されるでしょう:

  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          |

この練習問題のタスクは、eaxp をスタック機械の命令列に変換する小さなコンパイラ
を書き、その正当性を証明することです。

スタック言語の命令セットは、以下の命令から構成されます:

  * SPush n: 数 n をスタックにプッシュする。
  * SLoad X: ストアから識別子 X に対応する値を読み込み、スタックにプッシュす
    る。
  * SPlus: スタックの先頭の 2 つの数をポップし、それらを足して、結果をスタッ
    クにプッシュする。
  * SMinus: 上と同様。ただし引く。
  * SMult: 上と同様。ただし掛ける。
 *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(*
スタック言語のプログラムを評価するための関数を書きなさい。入力として、状態、
数のリストとして表現されたスタック (スタックの先頭要素はリストの先頭)、および
命令のリストとして表現されたプログラムを受け取り、受け取ったプログラムの実行
した後のスタックを返します。下にある例で、その関数のテストをしなさい。

上の仕様では、スタックが 2 つ未満の要素しか含まずに SPlus や SMinus、 SMult
命令に至った場合を明示していないままなことに注意しましょう。我々のコンパイラ
はそのような奇形のプログラムは生成しないので、これは重要でないという意味です
。しかし正当性の証明をするときは、いくつかの選択のほうが証明をより簡単にする
ことに気づくかもしれません。
 *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
admit.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5, SPush 3, SPush 1, SMinus]
   = [2, 5].
Admitted.

Example s_execute2 :
     s_execute (update empty_state X 3) [3,4]
       [SPush 4, SLoad X, SMult, SPlus]
   = [15, 4].
Admitted.

(*
次に、aexp をスタック機械のプログラムにコンパイルする関数を書きなさい。このプ
ログラムを実行する影響は、もとの式の値をスタックに積むことと同じでなければな
りません。
 *)

Fixpoint s_compile (e : aexp) : list sinstr :=
admit.

(*
最後に、compile 関数が正しく振る舞うことを述べている以下の定理を証明しなさい
。まずは使える帰納法の仮定を得るため、より一般的な補題を述べる必要があるでし
ょう。
 *)

Theorem s_compile_correct :
  forall (st : state) (e : aexp),
    s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
Admitted.
(* ☐ *)
