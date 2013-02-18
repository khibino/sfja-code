Require Export Poly.

Check (2 + 2 = 4).

Check (ble_nat 3 2 = false).

Check (2 + 2 = 5).

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition strange_prop1 : Prop :=
  (2 + 2 = 5) -> (99 + 26 = 42).

Definition strange_prop2 :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

Definition even (n:nat) : Prop :=
  evenb n = true.

Check even.
Check (even 4).
Check (even 3).

Definition even_n__even_SSn (n:nat) : Prop :=
  (even n) -> (even (S (S n))).

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat -> Prop := between 13 19.

Definition true_for_zero (P:nat -> Prop) : Prop :=
  P 0.

Definition preserved_by_S (P:nat -> Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P:nat -> Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P:nat -> Prop) : Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).


(* 根拠 *)

(* 帰納的に定義された命題 *)

Inductive good_day : day -> Prop :=
| gd_sat : good_day saturday
| gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before : day -> day -> Prop :=
| db_tue : day_before tuesday monday
| db_wed : day_before wednesday tuesday
| db_thu : day_before thursday wednesday
| db_fri : day_before friday thursday
| db_sat : day_before saturday friday
| db_sun : day_before sunday saturday
| db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day -> Prop :=
| fdfs_any : forall d:day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.


(* 証明オブジェクト *)

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.

Check fdfs_wed.
Check fdfs_wed'.

Inductive ok_day : day -> Prop :=
| okd_gd : forall d,
             good_day d ->
             ok_day d
| okd_before : forall d1 d2,
                 ok_day d2 ->
                 day_before d2 d1 ->
                 ok_day d1.

Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
             (okd_before thursday friday
                         (okd_before friday saturday
                                     (okd_gd saturday gd_sat)
                                     db_sat)
                         db_fri)
             db_thu.

Theorem okdw' : ok_day wednesday.
Proof.
  apply okd_before with (d2 := thursday).
    apply okd_before with (d2 := friday).
      apply okd_before with (d2 := saturday).
        apply okd_gd. apply gd_sat.
        apply db_sat.
      apply db_fri.
    apply db_thu. Qed.

Print okdw'.


(* 含意 *)

Definition okd_before2 := forall d1 d2 d3,
                           ok_day d3 ->
                           day_before d2 d1 ->
                           day_before d3 d2 ->
                           ok_day d1.


(* 練習問題: ★, optional (okd_before2_valid) *)

Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2.
  intros d1 d2 d3 ok b0 b1.
  apply okd_before with (d2 := d2).
    apply okd_before with (d2 := d3).
      apply ok.
    apply b1.
  apply b0.
Qed.
(* ☐ *)

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) =>
    fun (H : ok_day d3) =>
      fun (H0 : day_before d2 d1) =>
        fun (H1 : day_before d3 d2) =>
          okd_before d1 d2 (okd_before d2 d3 H H1) H0.

(*
練習問題: ★, optional (okd_before2_valid_defn)

下記の結果としてCoqが出力するものを予測しなさい。
 *)

(*
okd_before2_valid =
  fun (d1 d2 d3 : day) =>
    fun (ok : ok_day d3) =>
      fun (b0 : day_before d2 d1) =>
        fun (b1 : day_before d3 d2) =>
          okd_before d1 d2 (okd_before d2 d3 ok b1) b0 : okd_before2
 *)

(* Print okd_before2_valid. *)


(* 帰納的に定義された型に対する帰納法の原理 *)

Check nat_ind.


Theorem mult_0_r' :
  forall n:nat, n * 0 = 0.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
    reflexivity. Qed.


(*
練習問題: ★★ (plus_one_r')

induction タクティックを使わずに、下記の証明を完成させなさい。
 *)

Theorem plus_one_r' :
  forall n:nat, n + 1 = S n.
Proof.
  apply nat_ind.
  (* O *) reflexivity.
  (* S n *)
    intros n IHn.
    simpl. rewrite -> IHn. reflexivity.
Qed.
(* ☐ *)

Inductive yesno : Type :=
| yes : yesno
| no : yesno.

Check yesno_ind.

(*
練習問題: ★ (rgb)

次のデータ型に対してCoqが生成する帰納法の原理を予測しなさい。紙に答え
を書いたのち、Coqの出力と比較しなさい。
 *)

(* forall P : rgb -> Prop, P red -> P green -> P blue -> forall r : rgb, P r *)
Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.
(* ☐ *)

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.

(* Check natlist_ind. *)


(*
練習問題: ★ (natlist1)

上記の定義をすこし変えたとしましょう。

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 → nat → natlist1.

このとき、帰納法の原理はどのようになるでしょうか？
 *)

(*
natlist1_ind :
forall P : natlist1 -> Prop,
P nnil1 ->
(forall n : natlsit1, P n -> forall n0 : nat, P (nsnoc1 n n0)) ->
forall n : natlist, P n
 *)
(* ☐ *)

Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsnoc1 : natlist1 -> nat -> natlist1.

(* Check natlist1_ind. *)


(*
練習問題: ★ (ExSet)

帰納的に定義された集合に対する帰納法の原理が次のようなものだとします
。
      ExSet_ind :
         ∀ P : ExSet → Prop,
             (∀ b : bool, P (con1 b)) →
             (∀ (n : nat) (e : ExSet), P e → P (con2 n e)) →
             ∀ e : ExSet, P e

ExSet の帰納的な定義を示しなさい。
 *)

Inductive ExSet : Type :=
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet
.
(* ☐ *)

(* Check ExSet_ind. *)


(* Check list_ind. *)

(*
練習問題: ★ (tree)

次のデータ型に対してCoqが生成する帰納法の原理を予測しなさい。答えが書
けたら、それをCoqの出力と比較しなさい。

Inductive tree (X:Type) : Type :=
  | leaf : X → tree X
  | node : tree X → tree X → tree X.
Check tree_ind.
 *)

(*
tree_ind :
 forall (X : Type) (P : tree X -> Prop),
   (forall x : X, P (leaf X x)) ->
   (forall t : tree X, P t -> t0 : tree X, P t0 -> P (node X e e0)) ->
   forall t : tree X, P t
 *)
(* ☐ *)

Inductive tree (X:Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.
(* Check tree_ind. *)

(*
練習問題: ★ (mytype)

以下の帰納法の原理を生成する帰納的定義を探しなさい。
      mytype_ind :
        ∀ (X : Type) (P : mytype X → Prop),
            (∀ x : X, P (constr1 X x)) →
            (∀ n : nat, P (constr2 X n)) →
            (∀ m : mytype X, P m →
               ∀ n : nat, P (constr3 X m n)) →
            ∀ m : mytype X, P m
 *)

Inductive mytype (X:Type) : Type :=
| constr : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.
(* ☐ *)

(* Check mytype_ind. *)

(*
練習問題: ★, optional (foo)

以下の帰納法の原理を生成する帰納的定義を探しなさい。
      foo_ind :
        ∀ (X Y : Type) (P : foo X Y → Prop),
             (∀ x : X, P (bar X Y x)) →
             (∀ y : Y, P (baz X Y y)) →
             (∀ f1 : nat → foo X Y,
               (∀ n : nat, P (f1 n)) → P (quux X Y f1)) →
             ∀ f2 : foo X Y, P f2
 *)

Inductive foo (X Y:Type) :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.
(* ☐ *)

(* Check foo_ind. *)

(*
練習問題: ★, optional (foo')

次のような帰納的定義があるとします。

Inductive foo' (X:Type) : Type :=
  | C1 : list X → foo' X → foo' X
  | C2 : foo' X.

foo' に対してCoqはどのような帰納法の原理を生成するでしょうか? 空欄を埋め、Coqの結果と比較し
なさい
     foo'_ind :
        ∀ (X : Type) (P : foo' X → Prop),
              (∀ (l : list X) (f : foo' X),
                    _______________________ →
                    _______________________ ) →
             ___________________________________________ →
             ∀ f : foo' X, ________________________
 *)

(*
foo'_ind :
  forall (X : Type) (P : foo' X -> Prop),
    (forall (l : list X) (f : foo' X),
      P f ->
      P (C1 l f)) ->
    P C2 ->
    forall f : foo' X, P f
 *)

Inductive foo' (X:Type) : Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.

(* Check foo'_ind *)

(* ☐ *)


(* 帰納法の仮定 *)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition p_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' :
  forall n:nat, P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'".
    unfold P_m0r. simpl. intros n' IHn'.
    apply IHn'. Qed.


(* 偶数について再び *)

Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n:nat, ev n -> ev (S (S n)).


(*
練習問題: ★, optional (four_ev)

4が偶数であることをタクティックによる証明と証明オブジェクトによる証明で示しなさい。
 *)

Theorem four_ev' :
  ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Definition four_ev : ev 4 :=
  ev_SS _ (ev_SS _ ev_0).
(* ☐ *)

(*
練習問題: ★★ (ev_plus4)

n が偶数ならば 4+n も偶数であることをタクティックによる証明と証明オブジェクトによる証明で示しなさい。
 *)
Definition ev_plus4 : forall n, ev n -> ev (4 + n) :=
  fun n ev => ev_SS _ (ev_SS n ev).

Theorem ev_plus4' :
  forall n, ev n -> ev (4 + n).
Proof.
  simpl.
  intros n Hev.
  apply ev_SS. apply ev_SS. apply Hev.
Qed.

(* ☐ *)

(*
練習問題: ★★ (double_even)

次の命題をタクティックによって証明しなさい。
 *)

Theorem double_even :
  forall n, ev (double n).
Proof.
  induction n as [|n'].
  (* n = O *) apply ev_0.
  (* n = S n' *)
    simpl. apply ev_SS. apply IHn'. Qed.

(* ☐ *)

(*
練習問題: ★★★★, optional (double_even_pfobj)

上記のタクティックによる証明でどのような証明オブジェクトが構築されるかを予想しなさい。 
(答を確かめる前に、Case を除去しましょう。
 これがあると証明オブジェクトが少し見づらくなります。)

 *)

(* Check nat_ind. *)
(* nat_ind
      : forall P : nat -> Prop, 
        P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n *)

Definition double_even_pfobj : forall n, ev (double n) :=
  nat_ind (fun n => ev (double n))
          ev_0
          (fun (n' : nat) (IHn' : ev (double n')) => ev_SS (double n') IHn').
(* ☐ *)


(* 根拠に対する帰納法の推論 *)

Theorem ev_minus2 :
  forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.


(*
練習問題: ★ (ev_minus2_n)

E の代わりに n に対して destruct するとどうなるでしょうか?
 *)

Theorem ev_minus2_n :
  forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct n as [| n'].
  (* n = O *) apply ev_0.
  (* n = S n' *) destruct n' as [| n''].
    (* n = S n' = S O *) apply ev_0.
    (* n = S n' = S (S n'') *)
      simpl.
Admitted.
(* n に対する destruct だけでは示せない *)
(* ☐ *)


Theorem ev_even :
  forall n, ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'. Qed.


(*
練習問題: ★ (ev_even_n)

この証明を E でなく n に対する帰納法として実施できますか?
 *)
Theorem ev_even_n :
  forall n, ev n -> even n.
Proof.
  intros n E. induction n as [| n'].
  (* n = 0 *) reflexivity.
  (* n = S n' *) destruct n' as [| n''].
    (* n' = 0 *) inversion E.
    (* n' = S n'' n = S (S n'') *)
       inversion E. unfold even.
Admitted.

Theorem ev_even_n' :
  forall n, ev n -> even n.
Proof.
  intros n E. destruct n as [| n'].
  (* n = 0 *) reflexivity.
  (* n = S n' *) induction n' as [| n''].
    (* n' = 0 *) inversion E.
    (* n' = S n''  n = S (S n'') *)
      inversion E. unfold even. simpl.
Admitted.

(*
一つ前の n の帰納法の仮定のみでは証明がうまくいかない ☐
 *)

(*
練習問題: ★ (l_fails)

次の証明はうまくいきません。

     Theorem l : ∀ n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...

理由を簡潔に説明しない。
 *)

(* ev n の根拠を作る方法は n が偶数のときしか存在しないので。 *)
(* ☐ *)

(*
練習問題: ★★ (ev_sum)

帰納法が必要な別の練習問題をやってみましょう。
 *)

Theorem ev_sum :
  forall n m, ev n -> ev m -> ev (n+m).
Proof.
  intros n m evN evM.
  induction evN as [| n' evN'].
  (* evN = ev_0 *) apply evM.
  (* evN = ev_SS n' evN' *)
    simpl. apply ev_SS. apply IHevN'. Qed.
(* ☐ *)


Theorem SSev_ev_firsttry :
  forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'].
Admitted.

Theorem SSev_even :
  forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'. Qed.


(* 練習問題: ★ (inversion_practice) *)

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n evH.
  inversion evH as [| n' evH'].
  inversion evH' as [| n'' evH''].
  apply evH''.
Qed.

(*
inversion タクティックは、仮定が矛盾していることを示し、ゴールを
達成するためにも使えます。
 *)

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros evH.
  inversion evH as [| n evH'].
  inversion evH' as [| n' evH''].
  inversion evH''.
Qed.
(* ☐ *)

Theorem ev_minus2':
  forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.


(*
練習問題: ★★★ (ev_ev_even)

何に対して帰納法を行えばいいかを探しなさい。(ちょっとトリッキーで
すが)
 *)

Theorem ev_ev_even :
  forall n m,
    ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Enm E.
  generalize dependent Enm.
  generalize dependent m.
  induction E as [| n' E'].
  (* ev n = ev_0 *)  simpl. intros m Em. apply Em.
  (* ev n = ev_SS n' E' *)
    simpl. intros m Em. inversion Em as [| n'' Em'].
    apply (IHE' m Em'). Qed.
(* ☐ *)

(*
練習問題: ★★★, optional (ev_plus_plus)

既存の補題を適用する必要のある練習問題です。帰納法も場合分けも不要
ですが、書き換えのうちいくつかはちょっと大変です。 Basics_J.v の
plus_swap' で使った replace タクティックを使うとよいかもしれません
。
 *)

Theorem ev_plus_plus :
  forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p E0 E1.
  apply (ev_ev_even (n + n) (m + p)).
  rewrite <- (plus_assoc n n (m + p)).
  rewrite -> (plus_assoc n m p).
  rewrite -> (plus_comm n m).
  rewrite <- (plus_assoc m n p).
  rewrite -> (plus_assoc n m (n + p)).
  apply (ev_sum (n + m) (n + p)).
  apply E0. apply E1.
  rewrite <- double_plus.
  apply double_even.
Qed.
(* ☐ *)


(* なぜ命題を帰納的に定義するのか? *)

Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n:nat, MyProp n -> MyProp (4 + n)
  | MyProp3 : forall n:nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl.
  assert (12 = 4 + 8) as H12.
    Case "Proof of assertion". reflexivity.
  rewrite -> H12.
  apply MyProp2.
  assert (8 = 4 + 4) as H8.
    Case "Proof of assertion". reflexivity.
  rewrite -> H8.
  apply MyProp2.
  apply MyProp1. Qed.


(*
練習問題: ★★ (MyProp)

MyPropに関する便利な2つの事実があります。証明はあなたのために残し
てあります。
 *)

Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3. apply MyProp3. simpl.
  apply MyProp1. Qed.

Theorem MyProp_plustwo :
  forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros n H.
  apply MyProp3. simpl.
  assert (S (S (S (S n))) = 4 + n) as HP4.
  reflexivity.
  rewrite -> HP4.
  apply MyProp2. apply H. Qed.
(* ☐ *)


Theorem MyProp_ev :
  forall n:nat, ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  Case "E = ev_0".
    apply MyProp_0.
  Case "E = ev_SS n' E'".
    apply MyProp_plustwo. apply IHE'. Qed.


(* 練習問題: ★★★ (ev_MyProp) *)

Theorem ev_MyProp :
  forall n:nat, MyProp n -> ev n.
Proof.
  intros n E.
  induction E as [| n' E' | n' E'].
  (* E = MyProp1 *) apply (ev_SS 2 (ev_SS 0 ev_0)).
  (* E = MyProp2 *)
    simpl. apply ev_SS. apply ev_SS. apply IHE'.
  (* E = MyProp3 *)
    apply (ev_minus2 (S (S n')) IHE'). Qed.
(* ☐ *)

(*
練習問題: ★★★, optional (ev_MyProp_informal)

ev_MyProp の形式的な証明に対応する非形式的な証明を書きなさい。
 *)

(*
定理: すべての自然数 n に対して、 MyProp n ならば ev n。

証明: n を nat とし MyProp n の導出を E とする。
      E の帰納法について証明を行う。
      以下の 3つの場合を考える。

      - E の最後のステップが MyProp1 だった場合、n は 4 となる。
        その場合、ev 4 が成り立つことを示す必要がある。
        ev_SS 2 (ev_SS 0 ev_0) よりこれは真となる。

      - E の最後のステップが MyProp2 だった場合、
        n = 4 + n' となる n' が存在し、MyProp n' の導出が存在する。

        このときに ev n を示す必要がある。

        帰納法の仮定により ev n' の導出が存在するのでそれを
        IHE' とすると、 ev_SS (2 + n') (ev_SS n' IHE') は ev (4 + n') の導出となり、
        それは ev n の導出であるので示された。

      - E の最後のステップが MyProp3 だった場合、
        n = n' となる n' が存在し、 MyProp (2 + n') の導出が存在する。

        このときに ev n を示す必要がある。

        帰納法の仮定により ev (2 + n') の導出が存在するのでそれを
        IHE' とすると、ev_minus2 (S (S n')) IHE' は ev n' の導出となり、
        それは ev n の導出であるので示された。

        ☐
 *)
