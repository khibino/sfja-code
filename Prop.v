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
  Case "S". simpl. intros n IHn. apply IHn. Qed.


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


(* 全体像: Coqの2つの空間 *)

(* 値 *)

(* 型とカインド *)

(* 命題 vs. ブール値 *)

(* 関数 vs. 限量子 *)

(* 関数 vs. 含意 *)

(* 非形式的な証明 *)

(* 帰納法による非形式的な証明 *)

(* 帰納的に定義された集合についての帰納法 *)

(* 帰納的に定義された命題についての帰納法 *)

(* 選択課題 *)

(* induction タクティックについてもう少し *)


(*
練習問題: ★, optional (plus_explicit_prop)

plus_assoc' と plus_comm' を、その証明とともに上の mult_0_r'' と同
じスタイルになるよう書き直しなさい。このことは、それぞれの定理が帰
納法で証明された命題に明確な定義を与え、この定義された命題から定理
と証明を示しています。
 *)

Definition P_plus_assoc' (n m p : nat) : Prop :=
  n + (m + p) = (n + m) + p.

Theorem plus_assoc'' :
  forall n m p:nat, P_plus_assoc' n m p.
Proof.
  induction n as [| n'].
  Case "n = O". reflexivity.
  Case "n = S n'".
    unfold P_plus_assoc'. simpl.
    unfold P_plus_assoc' in IHn'.
    intros m p. rewrite -> IHn'. reflexivity. Qed.

Definition P_plus_comm' (n m : nat) : Prop :=
  n + m = m + n.

Theorem plus_comm''' :
  forall n m : nat, P_plus_comm' n m.
Proof.
  induction n as [| n'].
  Case "n = O".
    intros m. unfold P_plus_comm'.
    rewrite -> plus_0_r. reflexivity.
  Case "n = S n'".
    intros m.
    unfold P_plus_comm'. unfold P_plus_comm' in IHn'.
    simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity. Qed.
(* ☐ *)


(*
練習問題: ★★★★, optional (true_upto_n__true_everywhere)

true_upto_n_example を満たすような再帰関数
true_upto_n__true_everywhere を定義しなさい。
 *)

Fixpoint true_upto_n__true_everywhere (n:nat) (f:nat -> Prop) :=
  match n with
    | O => forall m, f m
    | S n' => f n -> true_upto_n__true_everywhere n' f
  end.

Example true_upto_n_example :
  (true_upto_n__true_everywhere 3 (fun n => even n))
    = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
(* ☐ *)


(* Prop における帰納法の原理 *)

Check ev_ind.

Theorem ev_even' : forall n, ev n -> even n.
Proof.
  apply ev_ind.
  Case "ev_0". unfold even. reflexivity.
  Case "ev_SS". intros n' E' IHE'. unfold even. apply IHE'. Qed.


(*
練習問題: ★★★, optional (prop_ind)

帰納的に定義された list と MyProp に対し、Coq がどのような帰納法の
原理を生成するか、予想して書き出し、次の行を実行した結果と比較しな
さい。
 *)
Check list_ind.
Check MyProp_ind.
(* ☐ *)

(*
練習問題: ★★★, optional (ev_MyProp')

もう一度 ev_MyProp を証明しなさい。ただし、今度は induction タクテ
ィックの代わりに apply MyProp_ind を使いなさい。
 *)

Theorem ev_MyProp' :
  forall n:nat, MyProp n -> ev n.
Proof.
  apply MyProp_ind.
  (* MyProp1 *) apply (ev_SS 2 (ev_SS 0 ev_0)).
  (* MyProp2 *)
    intros n P evH. simpl. apply ev_SS. apply ev_SS. apply evH.
  (* MyProp3 *)
    intros n P evH. apply (ev_minus2 (S (S n)) evH). Qed.
(* ☐ *)


(*
練習問題: ★★★★, optional (MyProp_pfobj)

もう一度 MyProp_ev と ev_MyProp を証明しなさい。ただし今度は、明確
な証明オブジェクトを手作業で構築（上の ev_plus4 でやったように）す
ることで証明しなさい。
 *)

(* Print MyProp_ev. *)
(* Print ev_ind. *)

(*
ev_ind =
fun (P : nat -> Prop) (f : P 0)
  (f0 : forall n : nat, ev n -> P n -> P (S (S n))) =>
fix F (n : nat) (e : ev n) {struct e} : P n :=
  match e in (ev n0) return (P n0) with
  | ev_0 => f
  | ev_SS n0 e0 => f0 n0 e0 (F n0 e0)
  end
     : forall P : nat -> Prop,
       P 0 ->
       (forall n : nat, ev n -> P n -> P (S (S n))) ->
       forall n : nat, ev n -> P n
*)

Definition MyProp_ev' (n:nat) (E:ev n) : MyProp n :=
  ev_ind MyProp MyProp_0 (fun n' _ => MyProp_plustwo n') n E.

Fixpoint MyProp_ev'' (n:nat) (E:ev n) : MyProp n :=
  match E in (ev n) return (MyProp n) with
    | ev_0 => MyProp_0
    | ev_SS n' E' => MyProp_plustwo n' (MyProp_ev' n' E')
  end.

(* Print MyProp_ind. *)

(*
MyProp_ind =
fun (P : nat -> Prop) (f : P 4)
  (f0 : forall n : nat, MyProp n -> P n -> P (4 + n))
  (f1 : forall n : nat, MyProp (2 + n) -> P (2 + n) -> P n) =>
fix F (n : nat) (m : MyProp n) {struct m} : P n :=
  match m in (MyProp n0) return (P n0) with
  | MyProp1 => f
  | MyProp2 n0 m0 => f0 n0 m0 (F n0 m0)
  | MyProp3 n0 m0 => f1 n0 m0 (F (2 + n0) m0)
  end
     : forall P : nat -> Prop,
       P 4 ->
       (forall n : nat, MyProp n -> P n -> P (4 + n)) ->
       (forall n : nat, MyProp (2 + n) -> P (2 + n) -> P n) ->
       forall n : nat, MyProp n -> P n
 *)

Definition ev_MyProp'' (n:nat) (pn:MyProp n) : ev n :=
  MyProp_ind ev
             (ev_SS 2 (ev_SS 0 ev_0))
             (fun n _ pn => ev_SS (S (S n)) (ev_SS n pn))
             (fun n _ pn => ev_minus2 (S (S n)) pn)
             n pn.
(* ☐ *)

Module P.

(*
練習問題: ★★★, optional (p_provability)

次の、帰納的に定義された命題について考えてみてください。：
 *)
Inductive p : (tree nat) -> nat -> Prop :=
   | c1 : forall n, p (leaf _ n) 1
   | c2 : forall t1 t2 n1 n2,
            p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (n1 + n2)
   | c3 : forall t n, p t n -> p t (S n).
(*
これについて、どのような時に p t n が証明可能であるか、その条件を
を自然言語で説明しなさい。
 *)
(*
葉が c1 で二分岐が c2 一分岐が c3 であるような木を考える。
葉のサイズは 1、 一分岐によるサイズの増分が 1、
二分岐のサイズは部分木の合計であるとする。
そのサイズを n としたとき、 t が同じ形の二分木のときには p t n が証明可能である。
☐
 *)

End P.


(* 追加練習問題 *)

(*
練習問題: ★★★★ (palindromes)

palindrome（回文）は、最初から読んでも逆から読んでも同じになるよう
なシーケンスです。

 ・ list X でパラメータ化され、それが palindrome であることを示す
    ような帰納的

命題 pal を定義しなさい。（ヒント：これには三つのケースが必要です
。この定義は、リストの構造に基いたものとなるはずです。まず一つのコ
ンストラクタ、

    c : forall l, l = rev l -> pal l

は明らかですが、これはあまりうまくいきません。）

 ・ 以下を証明しなさい。
           forall l, pal (l ++ rev l).

 ・ 以下を証明しなさい。
           forall l, pal l -> l = rev l.
 *)

Inductive pal'' {X:Type} : list X -> Prop :=
| pal_rev (l:list X) : l = rev l -> pal'' l.

Theorem id_plus_rev_pal'' :
  forall X (l:list X), pal'' (l ++ rev l).
Proof.
  intros X l. apply pal_rev.
  induction l as [| x xs ].
  (* l = [] *) reflexivity.
  (* l = x :: xs *)
    simpl.
    rewrite <- snoc_with_append. rewrite -> rev_snoc.
    rewrite <- IHxs. simpl. reflexivity. Qed.

Theorem pal''_id_rev_eq :
  forall X (l:list X), pal'' l -> l = rev l.
Proof.
  intros X l H. inversion H as [l' req]. apply req. Qed.


Inductive pal' {X:Type} : list X -> Prop :=
| pal_even (xs:list X) : pal' (xs ++ rev xs)
| pal_odd (x1:X) (xs:list X) : pal' (xs ++ x1 :: rev xs)
.

Theorem id_plus_rev_pal' :
  forall X (l:list X), pal' (l ++ rev l).
Proof. intros X. apply (@pal_even X). Qed.

Lemma app_nil :
  forall X (l:list X), l ++ [] = l.
Proof.
  intros X. induction l as [| x xs].
  (* l = [] *) reflexivity.
  (* l = x :: xs *) simpl. rewrite -> IHxs. reflexivity. Qed.

Lemma rev_app :
  forall X (l0:list X) (l1:list X), rev (l0 ++ l1) = rev l1 ++ rev l0.
Proof.
  intros X.
  induction l0 as [| x xs].
  (* l = [] *) simpl. intros l1. rewrite -> app_nil. reflexivity.
  (* l = x :: xs *)
    simpl. intros l1. rewrite <- snoc_with_append.
    rewrite -> IHxs. reflexivity. Qed.

Lemma rev_involutive :
  forall X (l:list X), rev (rev l) = l.
Proof.
  intros X l. induction l as [| x xs].
  Case "l = nil". reflexivity.
  Case "l = cons".
    simpl. rewrite -> rev_snoc. rewrite -> IHxs.
    reflexivity. Qed.

Lemma rev_injective :
  forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Theorem app_ass :
  forall X (l1 l2 l3 : list X),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros X l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Lemma snoc_cons_app :
  forall X (l1 l2 : list X) (x:X), (snoc l1 x) ++ l2 = l1 ++ x :: l2.
Proof.
  intros X l1 l2 x.
  assert (snoc (l1 ++ []) x = l1 ++ snoc [] x) as saH by apply snoc_with_append.
  simpl in saH. rewrite -> app_nil in saH.
  rewrite -> saH. rewrite -> app_ass.
  simpl. reflexivity. Qed.

Theorem pal'_id_rev_eq :
  forall X (l:list X), pal' l -> l = rev l.
Proof.
  intros X l palv.
  destruct palv as [xs | x1 xs].
  (* palv = pal_even xs *)
    rewrite -> rev_app. rewrite -> rev_involutive. reflexivity.
  (* palv = pal_odd x1 xs *)
    rewrite -> rev_app. simpl. rewrite -> rev_involutive.
    rewrite -> snoc_cons_app. reflexivity.
Qed.
(*
 *)

Inductive pal {X:Type} : list X -> Prop :=
| pal_0 : pal nil
| pal_1 : forall (x1:X), pal [x1]
| pal_next : forall (xs:list X) (xn:X), pal xs -> pal (xn :: snoc xs xn)
.

Theorem id_plus_rev_pal :
  forall X (l:list X), pal (l ++ rev l).
Proof.
  intros X l.
  induction l as [| x xs].
  (* l = [] *) simpl. apply pal_0.
  (* l = x :: xs *)
    simpl. rewrite  <- snoc_with_append. apply pal_next. apply IHxs.
Qed.

Theorem pal_id_rev_eq :
  forall X (l:list X), pal l -> l = rev l.
Proof.
  intros X l palv.
  induction palv as [| x1 | xs sn palv'].
  (* l = [] *) reflexivity.
  (* l = [x1] *) reflexivity.
  (* l = xn :: snoc xs xn *)
    simpl. rewrite -> rev_snoc.
    simpl. rewrite <- IHpalv'.
    reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★★★★, optional (palindrome_converse)

一つ前の練習問題で定義した pal を使って、これを証明しなさい。
     forall l, l = rev l -> pal l.
 *)

Theorem palindrome_converse'' :
  forall X (l:list X), l = rev l -> pal'' l.
Proof.
  intros X l. apply pal_rev. Qed.

Lemma rev_eq_decrease :
  forall X (x:X) (l:list X), x :: snoc l x = rev (x :: snoc l x) -> l = rev l.
Proof.
  intros X x l eq.
  simpl in eq. rewrite -> rev_snoc in eq. simpl in eq.
  inversion eq.
  apply (f_equal rev) in H0.
  rewrite -> rev_snoc in H0.
  rewrite -> rev_snoc in H0.
  inversion H0.
  rewrite -> rev_involutive in H1.
  symmetry. apply H1. Qed.

Inductive plist {X:Type} : list X -> Prop :=
| plist_0 : plist []
| plist_1 : forall (x:X), plist [x]
| plist_next : forall (x:X) (xs:list X), plist xs -> plist (x :: snoc xs x)
.

Lemma plist_revEq :
  forall X (l:list X), plist l -> l = rev l.
Proof.
  intros X l pl.
  induction pl as [| x | x xs pl' ].
  (* [] *)  reflexivity.
  (* [x] *) reflexivity.
  (* x :: xs *)
    simpl. rewrite -> rev_snoc. simpl.
    rewrite <- IHpl'. reflexivity.
Qed.

Lemma revEq_plist :
  forall X (l:list X), l = rev l -> plist l.
Proof.
  intros X l req.
  destruct l as [| x rx].
  (* [] *) apply plist_0.
  (* x :: rx *)
    simpl in req.
    induction (rev rx) as [| x' r] _eqn: eq.
    (* rx = [] *)
      apply (f_equal rev) in eq.
      simpl in eq. rewrite -> rev_involutive in eq.
      rewrite -> eq.
      apply plist_1.
    (* x :: snoc r x' *)
      apply (f_equal rev) in eq.
      simpl in eq. rewrite -> rev_involutive in eq.

      (* simpl in req. inversion req. rewrite <- H0 in H1. *)
      (* rewrite -> H1 in IHr. *)
Admitted.

Theorem palindrome_converse_plist :
  forall X (l:list X), plist l -> pal l.
Proof.
  intros X l pl.
  induction pl as [ e0 | x | x xs ppl ].
  (* [] *)  apply pal_0.
  (* [x] *) apply pal_1.
  (* x :: xs *)
    apply (pal_next xs x IHppl).
Qed. 

Theorem palindrome_converse :
  forall X (l:list X), l = rev l -> pal l.
Proof.
  intros X l req.
  apply palindrome_converse_plist.
  apply revEq_plist.
  exact req.
Qed.
(*
 *)
(* ☐ *)

(*
練習問題: ★★★★ (subsequence)

あるリストが、別のリストのサブシーケンス（ subsequence ）であると
は、最初のリストの要素が全て二つ目のリストに同じ順序で現れるという
ことです。ただし、その間に何か別の要素が入ってもかまいません。例え
ば、
    [1,2,3]

は、次のいずれのリストのサブシーケンスでもあります。
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]

しかし、次のいずれのリストのサブシーケンスでもありません。
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

 ・ list nat 上に、そのリストがサブシーケンスであることを意味する
    ような命題 subseq を定義しなさい。（ヒント：三つのケースが必要
    になります）
   
 ・ サブシーケンスである、という関係が「反射的」であることを証明し
    なさい。つまり、どのようなリストも、それ自身のサブシーケンスで
    あるということです。
   
 ・ 任意のリスト l1、 l2、 l3 について、もし l1 が l2 のサブシーケ
    ンスならば、 l1 は l2 ++ l3 のサブシーケンスでもある、というこ
    とを証明しなさい。.
   
 ・ （これは少し難しいですので、任意とします）サブシーケンスという
    関係は推移的である、つまり、 l1 が l2 のサブシーケンスであり、
    l2 が l3 のサブシーケンスであるなら、 l1 は l3 のサブシーケン
    スである、というような関係であることを証明しなさい。（ヒント：
    何について帰納法を適用するか、よくよく注意して下さい。）

☐

練習問題: ★★, optional (foo_ind_principle)

次のような、帰納的な定義をしたとします：
   Inductive foo (X : Set) (Y : Set) : Set :=
     | foo1 : X → foo X Y
     | foo2 : Y → foo X Y
     | foo3 : foo X Y → foo X Y.

次の空欄を埋め、この定義のために Coq が生成する帰納法の原理を完成
させなさい。

   foo_ind
        : ∀ (X Y : Set) (P : foo X Y → Prop),
          (∀ x : X, __________________________________) →
          (∀ y : Y, __________________________________) →
          (________________________________________________) →
           ________________________________________________

☐

練習問題: ★★, optional (bar_ind_principle)

次に挙げた帰納法の原理について考えてみましょう：
   bar_ind
        : ∀ P : bar → Prop,
          (∀ n : nat, P (bar1 n)) →
          (∀ b : bar, P b → P (bar2 b)) →
          (∀ (b : bool) (b0 : bar), P b0 → P (bar3 b b0)) →
          ∀ b : bar, P b

これに対応する帰納的な集合の定義を書きなさい。
   Inductive bar : Set :=
     | bar1 : ________________________________________
     | bar2 : ________________________________________
     | bar3 : ________________________________________.

☐

練習問題: ★★, optional (no_longer_than_ind)

次のような、帰納的に定義された命題が与えられたとします：
  Inductive no_longer_than (X : Set) : (list X) → nat → Prop :=
    | nlt_nil : ∀ n, no_longer_than X [] n
    | nlt_cons : ∀ x l n, no_longer_than X l n →
                               no_longer_than X (x::l) (S n)
    | nlt_succ : ∀ l n, no_longer_than X l n →
                             no_longer_than X l (S n).

この命題のために Coq が生成する帰納法の原理を完成させなさい。
  no_longer_than_ind
       : ∀ (X : Set) (P : list X → nat → Prop),
         (∀ n : nat, ____________________) →
         (∀ (x : X) (l : list X) (n : nat),
          no_longer_than X l n → ____________________ →
                                  _____________________________ →
         (∀ (l : list X) (n : nat),
          no_longer_than X l n → ____________________ →
                                  _____________________________ →
         ∀ (l : list X) (n : nat), no_longer_than X l n →
           ____________________

☐

練習問題: ★★, optional (R_provability)

Coq に次のような定義を与えたとします：
    Inductive R : nat → list nat → Prop :=
      | c1 : R 0 []
      | c2 : ∀ n l, R n l → R (S n) (n :: l)
      | c3 : ∀ n l, R (S n) l → R n l.

次のうち、証明可能なのはどの命題でしょうか？

 ・ R 2 [1,0]
 ・ R 1 [1,2,1,0]
 ・ R 6 [3,2,1,0]

☐
 *)
