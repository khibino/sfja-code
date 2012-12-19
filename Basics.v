
Inductive day : Type :=
  | monday    : day
  | tuesday   : day
  | wednesday : day
  | thursday  : day
  | friday    : day
  | saturday  : day
  | sunday    : day
.

Definition next_weekday (d:day) : day :=
  match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
(next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true  : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true  => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true  => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true  => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true ) = true.
Proof. simpl. reflexivity. Qed.

Definition admit {T: Type} : T. Admitted.


(*
練習問題: ★ (nandb)

次の定義を完成させ、Exampleで記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。

この関数はどちらか、もしくは両方がfalseになったときにtrueを返すものである。
 *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).
  (* match b1 with *)
  (*   | true  => negb b2 *)
  (*   | false => true *)
  (* end. *)

(* 下の定義からAdmitted.を取り去り、代わりに"Proof. simpl. reflexivity. Qed."で検証できるようなコードを記述しなさい。 *)

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
(* ☐ *)


(* 練習問題: ★ (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | true  => andb b2 b3
    | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check (negb true).
Check negb.

Module Playground1.

Require Import Coq.Unicode.Utf8_core.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat
.

Definition pred (n : nat) : nat :=
  match n with
    | O    => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O   => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O   => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(* Example test_exp99: (exp 3 3) = 27. *)
(* Proof. simpl. reflexivity. Qed. *)


(* 演習問題: ★ (factorial) *)

(* 再帰を使用した、一般的なfactorical（階乗）の定義を思い出してください : *)

(*     factorial(0)  =  1 *)
(*     factorial(n)  =  n * factorial(n-1)     (if n>0) *)

(* これをCoqでの定義に書き直しなさい。 *)

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

(* Module Playground20. *)

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

(* End Playground20. *)

(* Check (0%nat). *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
             | O => true
             | S m' => false
           end
    | S n' => match m with
                | O => false
                | S m' => beq_nat n' m'
              end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
        match m with
          | O => false
          | S m' => ble_nat n' m'
        end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* 練習問題: ★★ (blt_nat) *)

(* blt_nat関数は、自然数を比較して小さい、ということを調べてbool *)
(* 値を生成します（ natural numbers for less-than）。Fixpointを *)
(* 使用して１から作成するのではなく、すでにこれまで定義した関数 *)
(* を利用して定義しなさい。 *)

(* 注：simplタクティックを使ってうまくいかない場合は、代わりに *)
(* computeを試してください。それはよりうまく作られたsimplと言え *)
(* るものですが、そもそもシンプルでエレガントな解が書けていれば *)
(* 、simplで十分に評価できるはずです。 *)

Definition blt_nat (n m : nat) : bool :=
  andb (negb (beq_nat n m)) (ble_nat n m).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Require Import Coq.Unicode.Utf8_core.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  simpl. reflexivity. Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  reflexivity. Qed.

(* 練習問題: ★, optional (simpl_plus) *)

(* この問い合わせの結果、Coqが返す応答はなにか？ *)

Eval simpl in (forall n:nat, n + 0 = n). (* 右単位元が証明されていない *)

(* また次のものの場合はどうか？ *)

Eval simpl in (forall n:nat, 0 + n = n). (* 左単位元は証明されている *)

(* この二つの違いを示せ。 ☐ *)


Theorem plus_O_n'' : forall n:nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.


Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m. intros H. rewrite -> H. reflexivity. Qed.

(*
Theorem plus_id_example' : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m. intros H. rewrite <- H. reflexivity. Qed.
 *)

(*
練習問題: ★ (plus_id_exercise)

Admitted.を削除し、証明を完成させなさい。
 *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o. intros H0 H1. rewrite -> H0, <- H1. reflexivity. Qed.
(* ☐ *)


Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.


(* 練習問題: ★★, recommended (mult_1_plus) *)

Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  intros n m.
  rewrite -> plus_1_l.
  reflexivity. Qed.
(* ☐ *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. simpl. Admitted.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.

(*
Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n']; reflexivity. Qed.
*)

(* 練習問題: ★ (zero_nbeq_plus_1) *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.
(* ☐ *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
    | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
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

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity. Qed.

(*
練習問題: ★★ (andb_true_elim2)

destructを使い、case（もしくはsubcase）を作成して、以下の証明andb_true_elim2を完成させなさい
。
*)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
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

(*
  destruct b.
  Case "b = true".
    rewrite <- H.
    reflexivity.
  Case "b = false".
    inversion H. Qed.
*)

(* ☐ *)

Theorem plus_0_r_firsttry : forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  simpl. Admitted.

Theorem plus_0_r_secondtry : forall n : nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. Admitted.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.


(* 練習問題: ★★, recommended (basic_induction) *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

(* ☐ *)


Fixpoint double (n:nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.


(* 練習問題: ★★ (double_plus) *)

Lemma double_plus : ∀ n, double n = n + n .
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
   simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.
(* ☐ *)


(*
練習問題: ★ (destruct_induction)

destructとinductionの違いを短く説明しなさい。
*)

(* induction だけ Induction Hypothesis を使える。 *)

(* ☐ *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = Sn'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

(*
練習問題: ★★ (plus_comm_informal)

plus_commの証明を、非形式的な証明に書き換えなさい。

定理：加法は可換である。
 *)

(*
Proof: ☐
*)
