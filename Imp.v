
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

(* ☐ *)

(* 練習問題: ★★★★, optional (optimizer) *)

(*
設計練習: 定義したoptimize_0plus関数で実装された最適化は、算術式やブール
式に対して考えられるいろいろな最適化の単なる1つに過ぎません。より洗練さ
れた最適化関数を記述し、その正しさを証明しなさい。
 *)

(* ☐ *)


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
