
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
  intros n m o.
  intros H0 H1.
  rewrite -> H0, <- H1.
  reflexivity.
Qed.
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
Proof: ☐
 *)

(*
定理 : 任意の n m について以下が成り立つ
  n + m = m + n

証明 : n について帰納法を適用する。
  ☐ まず n = 0 と置くと以下のようになる
       0 + m = m + 0
     + の定義から
          m = m + 0
     加法+ の右単位元の定理(plus_0_r)から示される
  ☐ 次に n = S n' と置き、帰納法の仮定を
       n' + m = m + n'
     とすると、以下のような式が成り立つ。
       S (n' + m) = S (m + n')
     また加法の左+1の定理(plus_n_Sm)から
       S (m + n') = m + S n'
     したがって、
       S (n' + m) = m + S n'
     ここで加法+ の定義より、以下のように変形できる。
       S n' + m = m + S n'
     これは、直後の値について帰納法の仮定が成り立つことを示している。 ☐
 *)

(*
練習問題: ★★, optional (beq_nat_refl_informal)

次の証明を、plus_assoc の非形式的な証明を参考に書き換えなさい。Coqのタクティックを単に言い換えただけにならないように！

定理：true=beq_nat n n forany n.（任意のnについて、nはnと等しいという命題がtrueとなる）
Proof: ☐
*)

(*
定理 : true = beq_nat n n forany n.
証明 : n について帰納法を適用する。
  ☐ まず n = 0 と置くと以下のようになる
       true = beq_nat 0 0
     これは beq_nat の定義から示される
  ☐ 次に n = S n' と置き、帰納法の仮定を
       true = beq_nat n' n'
     とする。
     ここで beq_nat の定義により、以下のように変形できる。
       true = beq_nat (S n') (S n')
     これは、直後の値について帰納法の仮定が成り立つことを示している。 ☐
 *)

(*
練習問題: ★, optional (beq_nat_refl)
*)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. reflexivity. Qed.
(* ☐ *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry :
  forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Admitted.


Theorem plus_rearrange :
  forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. Qed.

(* Print plus_rearrange. *)


(*
練習問題: ★★★★ (mult_comm)

assertを使用して以下の証明を完成させなさい。ただしinduction（帰納法）を使用しないこと。
 *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
    Case "Proof assertion".
    rewrite -> plus_comm.
    reflexivity.
  rewrite <- H.
  reflexivity.
  Qed.

(*
では、乗法が可換であることを証明しましょう。おそらく、補助的な定理を定義し、それを使って全体を証明することになると思います。先ほど証明したplus_swapが便利に使えるでしょう。
 *)

Theorem mult_succ_r :
  forall n m : nat,
    n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> plus_swap.
    rewrite <- IHn'.
    reflexivity.
  Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros n m.
  induction n as [| n'].
    induction m as [| m'].
    Case "n = 0, m = 0".
      reflexivity.
    Case "n = 0, m = S m'".
      rewrite -> mult_0_r.
      reflexivity.
    induction m as [| m'].
    Case "n = S n', m = 0".
      rewrite -> mult_0_r.
      reflexivity.
    Case "n = S n', m = S m'".
      simpl.
      rewrite -> IHn'.
      rewrite -> mult_succ_r.
      rewrite -> plus_swap.
      simpl.
      reflexivity.
    Qed.

(* ☐ *)


(* 練習問題: ★★, optional (evenb_n__oddb_Sn) *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl.
    assert (H: forall b:bool, negb (negb b) = b).
      intros b. destruct b. reflexivity. reflexivity.
    rewrite -> IHn'.
    rewrite -> H.
    simpl.
    reflexivity.
  Qed.
(* ☐ *)

(*
さらなる練習問題

練習問題: ★★★, optional (more_exercises)

紙を何枚か用意して、下に続く定理が(a)簡約と書き換えだけで証明可能か、(b)destructを使ったcase分割が必
要になるか、(c)帰納法が必要となるか、のいずれに属すかを、紙の上だけで考えなさい。予測を紙に書いたら
、実際に証明を完成させなさい。証明にはCoqを用いてかまいません。最初に紙を使ったのは「初心忘れるべか
らず」といった理由です。
*)

(*
引数にデータコンストラクタが無いので簡約できない。
また、destruct しても再帰的に仮定が必要になる。
 (c)
 *)
Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. reflexivity. Qed.

(*
簡約の時点でデータコンストラクタの区別で判定できる。
 (a)
 *)
Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n. reflexivity. Qed.

(*
左側の引数にデータコンストラクタがあらわれていないので場合分けする必要がある。
bool は有限データなので帰納法は必要ない。
 (b)
 *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b. reflexivity. reflexivity. Qed.

(*
引数にデータコンストラクタが無いので簡約できない。
また、destruct しても再帰的に仮定が必要になる。
 (c)
 *)
Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true → ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H. induction p as [| p'].
  Case "p = 0".
    simpl. rewrite -> H. reflexivity.
  Case "p = S p'".
    simpl. rewrite -> IHp'. reflexivity. Qed.

(*
簡約の時点でデータコンストラクタの区別で判定できる。
 (a)
 *)
Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. reflexivity. Qed.

(*
簡約できるが、その後、加法で帰納法が必要になる。
 (c)
 *)
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

(*
引数にデータコンストラクタが無いので簡約できない。
bool は有限データなので帰納法は必要ない。
 (b)
 *)
Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c. destruct b. destruct c.
  reflexivity. reflexivity. reflexivity. Qed.

(*
引数にデータコンストラクタが無いので簡約できない。
また、destruct しても再帰的に仮定が必要になる。
 (c)
 *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction p as [| p'].
  Case "p = 0".
    rewrite -> mult_0_r. rewrite -> mult_0_r. rewrite -> mult_0_r.
    reflexivity.
  Case "p = S p'".
    rewrite -> mult_succ_r.
    rewrite -> mult_succ_r.
    rewrite -> mult_succ_r.
    rewrite -> plus_swap.
    rewrite <- plus_assoc.
    rewrite <- plus_assoc.
    rewrite <- IHp'.
    rewrite -> plus_swap.
    reflexivity.
  Qed.

(*
引数にデータコンストラクタが無いので簡約できない。
また、destruct しても再帰的に仮定が必要になる。
 (c)
 *)
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> mult_plus_distr_r. rewrite -> IHn'.
    reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★, optional (plus_swap')

replaceタクティックは、特定のサブタームを置き換えたいものと置き換えることができます。もう少し正確に
言うと、replace (t) with (u)は、ゴールにあるtという式を全てuにかきかえ、t = uというサブゴールを追加
します。この機能は、通常のrewriteがゴールの思い通りの場所に作用してくれない場合に有効です。

replaceタクティックを使用してplus_swap'の証明をしなさい。ただしplus_swapのようにassert (n + m = m + 
n)を使用しないで証明を完成させなさい。
*)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> plus_assoc. rewrite -> plus_assoc.
  replace (m + n) with (n + m). reflexivity.
  rewrite -> plus_comm. reflexivity. Qed.

(* ☐ *)

(*
練習問題: ★★★★, recommended (binary)

これまでとは異なる、通常表記の自然数ではなく2進のシステムで、自然数のより効率的な表現を考えなさい。
それは自然数をゼロとゼロに1を加える加算器からなるものを定義する代わりに、以下のような2進の形で表すも
のです。2進数とは、

 ・ ゼロであるか,
 ・ 2進数を2倍したものか,
 ・ 2進数を2倍したものに1を加えたもの.

(a) まず、以下のnatの定義に対応するような2進型binの帰納的な定義を完成させなさい。 (ヒント: nat型の定
義を思い出してください。
    Inductive nat : Type :=
      | O : nat
      | S : nat → nat.
nat型の定義OやSの意味が何かを語るものではなく、（Oが実際に何であろうが）Oがnatであって、nがnatならS
が何であろうとS nはnatである、ということを示しているだけです。「Oがゼロで、Sは1を加える」という実装
がそれを自然数としてみて実際に関数を書き、実行したり証明したりしてみてはじめて実際に意識されます。こ
こで定義するbinも同様で、次に書く関数が書かれてはじめて型binに実際の数学的な意味が与えられます。)
 *)

Inductive bin : Type :=
  | B0 : bin
  | Be : bin -> bin
  | Bo : bin -> bin
.

(*
(b) 先に定義したbin型の値をインクリメントする関数を作成しなさい。また、bin型をnat型に変換する関数も
作成しなさい。
 *)

Fixpoint inc_bin (b : bin) : bin :=
  match b with
    | B0 => Bo B0
    | Be b' => Bo b'
    | Bo b' => Be (inc_bin b')
  end.

Fixpoint bin2nat (b : bin) : nat :=
  match b with
    | B0 => O
    | Be b' => 2 * bin2nat b'
    | Bo b' => 1 + 2 * bin2nat b'
  end.

Example bin2nat_sixteen : bin2nat (Be (Be (Be (Be (Bo B0))))) = 16.
Proof. reflexivity. Qed.

Example bin2nat_twenty_one : bin2nat (Bo (Be (Bo (Be (Bo B0))))) = 21.
Proof. reflexivity. Qed.

(*
(c) 最後にbで作成したインクリメント関数と、2進→自然数関数が可換であることを証明しなさい。これを証明
するには、bin値をまずインクリメントしたものを自然数に変換したものが、先に自然数変換した後にインクリ
メントしたものの値と等しいことを証明すればよい。
 *)

Theorem bin2nat_inc_bin_comm :
  forall b : bin, bin2nat (inc_bin b) = S (bin2nat b).
Proof.
  intros b.
  induction b as [| be | bo].
    Case "b = B0". reflexivity.
    Case "b = Be be".
      simpl. reflexivity.
    Case "b = Bo bo".
      simpl.
      rewrite -> plus_0_r.
      rewrite -> plus_0_r.
      rewrite -> IHbo.
      rewrite <- plus_n_Sm.
      simpl.
      reflexivity.
    Qed.
(* ☐ *)

(*
練習問題: ★★★★★ (binary_inverse)

この練習問題は前の問題の続きで、2進数に関するものである。前の問題で作成された定義や定理をここで用い
てもよい。

(a) まず自然数を2進数に変換する関数を書きなさい。そして「任意の自然数からスタートし、それを2進数にコ
ンバートし、それをさらに自然数にコンバートすると、スタート時の自然数に戻ることを証明しなさい。
*)

Fixpoint nat2bin (n:nat) : bin :=
  match n with
    | O => B0
    | S n' => inc_bin (nat2bin n')
  end.

Theorem nat_bin_nat : forall n:nat, bin2nat (nat2bin n) = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> bin2nat_inc_bin_comm. rewrite -> IHn'.
    reflexivity. Qed.

(*
(b) あなたはきっと、逆方向についての証明をしたほうがいいのでは、と考えているでしょう。それは、任意の
2進数から始まり、それを自然数にコンバートしてから、また2進数にコンバートし直したものが、元の自然数と
一致する、という証明です。しかしながら、この結果はtrueにはなりません。！！その原因を説明しなさい。
*)

(* 数値に対して nat 一通りに表現が決定されるが、bin は複数の表現がありうるため。 *)

(*
(c) 2進数を引数として取り、それを一度自然数に変換した後、また2進数に変換したものを返すnormalize関数
を作成し、証明しなさい。
*)

Definition normalize (b:bin) : bin := nat2bin (bin2nat b).

Theorem normalize_refl : forall b:bin, normalize b = nat2bin (bin2nat b).
Proof. reflexivity. Qed.

Theorem normalized_idempotent : forall b:bin, normalize (normalize b) = normalize b.
Proof.
  intros b.
  rewrite -> normalize_refl.
  rewrite -> normalize_refl.
  rewrite -> nat_bin_nat.
  reflexivity. Qed.

(*
練習問題: ★★, optional (decreasing)

各関数の引数のいくつかが"減少的"でなければならない、という要求仕様は、Coqのデザインにおいて基礎とな
っているものです。特に、そのことによって、Coq上で作成された関数が、どんな入力を与えられても必ずいつ
か終了する、ということが保障されています。しかし、Coqの"減少的な解析"が「とても洗練されているとまで
はいえない」ため、時には不自然な書き方で関数を定義しなければならない、ということもあります。

これを具体的に感じるため、Fixpointで定義された、より「微妙な」関数の書き方を考えてみましょう（自然数
に関する簡単な関数でかまいません）。それが全ての入力で停止することと、Coqがそれを、この制限のため受
け入れてくれないことを確認しなさい。
*)

Fixpoint down_to_zero (n:nat) : nat :=
  match oddb n with
    | true => (* down_to_zero (S n) *)
              match n with
                | S n' => down_to_zero n'
                | n'   => n'
              end
    | false => match n with
                 | S (S n') => down_to_zero n'
                 | n'       => n'
               end
  end.

(*
奇数だったら 1を加え、偶数だったら 2以上なら2引く。0 なら終了する関数。
Coqを通すために 1 を加える代わりに 1を引いている。
 *)

Eval simpl in (down_to_zero 15).

(* ☐ *)
