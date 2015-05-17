Require Export "Prop".

Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).

Definition funny_prop1'' := forall n, ev n -> ev (n+4).

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example :
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print and_example.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left".  apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem proj1 : forall P Q : Prop,
                  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.


(* 練習問題: ★, optional (proj2) *)

Theorem proj2 : forall P Q : Prop,
                  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ. Qed.
(* ☐ *)


Theorem and_commut : forall P Q : Prop,
                       P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
  apply HQ.
  apply HP. Qed.

Print and_commut.

(*
練習問題: ★★ (and_assoc)

次の証明では、inversionが、入れ子構造になった命題H : P ∧ (Q ∧ R)をどのようにHP:
P, HQ : Q, HR : R に分解するか、という点に注意しなががら証明を完成させなさい。
 *)

Theorem and_assoc : forall P Q R : Prop,
                      P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR.
Qed.
(* ☐ *)

(*
練習問題: ★★, recommended (even_ev)

今度は、前の章で棚上げしていた even と ev の等価性をが別の
方向から証明してみましょう。ここで左側のandは我々が実際に注
目すべきものです。右のandは帰納法の仮定となって帰納法による
証明に結びついていくことになるでしょう。なぜこれが必要とな
るかは、左側のandをそれ自身で証明しようとして、行き詰まって
みるとかるでしょう。
 *)

Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intro n.
  unfold even.
  induction n as [| n'].
  (* n = 0 *)
    simpl. split.
    intros eq. apply ev_0.
    intros eq. discriminate eq.
  (* n = S n' *)
    inversion IHn' as [Hn' HSn'].
    split.
    apply HSn'.
    simpl.
    intros eeqH.
    apply ev_SS.
    apply (Hn' eeqH).
Qed.
(* ☐ *)


(*
練習問題: ★★

次の命題の証明を示すオブジェクトを作成しなさい。
 *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) H0 H1 =>
    match H0 with
      | conj HP0 HQ0 =>
        match H1 with
          | conj HQ1 HR1 => conj P R HP0 HR1
        end
    end.
(* ☐ *)

(* Iff （両含意） *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB. Qed.

(* 練習問題: ★ (iff_properties)

上の、 ↔ が対称であることを示す証明 (iff_sym) を使い、それが反射的であること、推移的であることを証明しなさい
。
 *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intro P.
  split.
  intro P0. apply P0.
  intro P0. apply P0.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H0 H1.
  inversion H0 as [ HPQ HQP ].
  inversion H1 as [ HQR HRQ ].
  split.
  intro p. apply (HQR (HPQ p)).
  intro r. apply (HQP (HRQ r)).
Qed.

(*
ヒント: もしコンテキストに iff を含む仮定があれば、 inversion を使ってそれを二つの含意の式に分割することがで
きます。 (なぜそうできるのか考えてみましょう。)
 *)
(* ☐ *)

(*
練習問題: ★★ (MyProp_iff_ev)

ここまで、MyProp や ev がこれらの命題がある種の数値を特徴づける（偶数、などの）ことを見てきました。次の
MyProp n ↔ ev n が任意の nで成り立つことを証明しなさい。お遊びのつもりでかまわないので、その証明を、単純明快
な証明、タクティックを使わないにような証明に書き換えてください。（ヒント：以前に使用した定理をうまく使えば、
１行だけでかけるはずです！）
 *)
Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  fun (n : nat) => conj (MyProp n -> ev n) (ev n -> MyProp n) (ev_MyProp n) (MyProp_ev n).
(* ☐ *)

(*
Coqのいくつかのタクティックは、証明の際に低レベルな操作を避けるため iff を特別扱いします。特に rewrite を iff
に使うと、単なる等式以上のものとして扱ってくれます。
 *)

(* 論理和、選言（Disjunction、OR） *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.

Check or_intror.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". apply or_intror. apply HP.
    Case "left". apply or_introl. apply HQ. Qed.

Theorem or_commut' : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". right. apply HP.
    Case "left". left. apply HQ. Qed.


(*
練習問題: ★★ optional (or_commut'')

or_commut の証明オブジェクトがどのようになるか、書き出してみてください。（ただし、定義済みの証明オブジェクト
を Print を使って見てみたりしないこと。）
 *)
Definition or_commut'' : forall P Q : Prop, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) H =>
    match H with
      | or_introl HP => or_intror Q P HP
      | or_intror HQ => or_introl Q P HQ
    end.
(* ☐ *)

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR. Qed.

(*
練習問題: ★★, recommended (or_distributes_over_and_2)
 *)

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [ [PH0 | QH] [PH1 | RH] ].
  left. apply PH0.
  left. apply PH0.
  left. apply PH1.
  right. split. apply QH. apply RH.
Qed.
(* ☐ *)

(*
練習問題: ★ (or_distributes_over_and)
 *)

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  (* -> *)
    intro H.
    inversion H as [ PH | [ QH RH ] ].
    (* P *)
      split.
      left. apply PH.
      left. apply PH.
    (* Q /\ R*)
      split.
      right. apply QH.
      right. apply RH.
  (* <- *)
    intro H.
    inversion H as [ [PH0 | QH] [PH1 | RH] ].
    left. apply PH0.
    left. apply PH0.
    left. apply PH1.
    right. split. apply QH. apply RH.
Qed.
(* ☐ *)


(* ∧ 、 ∨ のandb 、orb への関連付け *)

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H. Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(*
練習問題: ★ (bool_prop)
 *)

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
    destruct c.
    (* b = true, c = true *)
      simpl in H.
      inversion H.

    (* b = true, c = false *)
      right. reflexivity.

  (* b = false *)
    left. reflexivity.
Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
    left. reflexivity.

    destruct c.
      right. reflexivity.

      simpl in H.
      inversion H.
Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      simpl in H. inversion H.

      simpl in H. inversion H.

    destruct c.
      simpl in H. inversion H.

      split. reflexivity. reflexivity.
Qed.
(* ☐ *)

(* 偽であるということ *)

(* Inductive False : Prop := . *)
Check False_ind.

(*
練習問題: ★ (False_ind_principle)

「偽」に関する帰納的な公理を何か思いつくことができますか？
 *)

(* 帰納的な命題は無い? *)

(* ☐ *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra. Qed.


(* 真であるということ *)

(*
練習問題: ★★ (True_induction)

True を、帰納的な命題として定義しなさい。あなたの定義に対してCoqはどのような帰納的原理を生成してくれるでしょ
うか。（直観的には True はただ当たり前のように根拠を示される命題であるべきです。代わりに、帰納的原理から帰納
的な定義を逆にたどっていくほうが近道だと気づくかもしれません。）
 *)

Inductive MyTrue : Prop :=
| T : MyTrue.

Check MyTrue_ind.
Check True_ind.

(* ☐ *)


(* 否定 *)

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~ P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

(*
練習問題: ★★, recommended (double_neg_inf)

double_neg の非形式的な証明を書きなさい。:

Theorem: P implies ~~P, for any proposition P.
 *)

(* Proof: ☐ *)

(*
練習問題: ★★, recommended (contrapositive)
 *)

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q f nq p.
  apply (nq (f p)).
Qed.
(* ☐ *)

(*
練習問題: ★ (not_both_true_and_false)
 *)

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  intros P H.
  inversion H as [ p np ].
  apply (np p).
Qed.
(* ☐ *)

Theorem five_not_even :
  ~ ev 5.
Proof.
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1. Qed.

(*
練習問題: ★ ev_not_ev_S

定理 five_not_even は、「５は偶数ではない」というようなとても当たり前の事実を確認するものです。今度はもう少し
面白い例です。
 *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H.
  (* ev_0 *)  intro H. inversion H.
  (* ev_SS *)
    intro H2.
    inversion H2 as [| n' evH ].
    apply (IHev evH).
Qed.
(* ☐ *)

(*
練習問題: ★ (informal_not_PNP)

命題 ∀ P : Prop, ~(P ∧ ~P) の形式的でない証明を（英語で）書きなさい。
 *)

(* ☐ *)

Theorem classic_double_neg : forall P : Prop,
  ~~ P -> P.
Proof.
  intros P H. unfold not in H.
  Admitted.

(*
練習問題: ★★★★★, optional (classical_axioms)

さらなる挑戦を求める人のために、 Coq'Art book (p. 123) から一つ練習問題を取り上げてみます。次の五つの文は、よ
く「古典論理の特性」と考えられているもの（Coqにビルトインされている構成的論理の対極にあるもの）です。これらを
Coqで証明することはできませんが、古典論理を使うことが必要なら、矛盾なく「証明されていない公理」として道具に加
えることができます。これら五つの命題が等価であることを証明しなさい。
 *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~ P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~ P /\ ~ Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q)  -> (~ P \/ Q).

(* ☐ *)


(* 不等であるということ *)

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity. Qed.

(*
練習問題: ★★, recommended (not_eq_beq_false)
 *)

Lemma eq_nat_dec :
  forall n m : nat, S n <> S m -> n <> m.
Proof.
  intros n m H eq. apply H.
  rewrite <- eq. reflexivity.
Qed.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' ].
  (* m = 0 *)
    destruct n as [| n' ].
    (* n = 0 *)
      intros H.
      apply ex_falso_quodlibet. apply H.
      reflexivity.
    (* n = S n' *)
      intros H. reflexivity.
  (* m = S m' *)
    destruct n as [| n' ].
    (* n = 0 *) intros H. reflexivity.
    (* n = S n' *)
      intros H. simpl.
      apply IHm'.
      apply eq_nat_dec.
      exact H.
Qed.
(* ☐ *)

(*
練習問題: ★★, optional (beq_false_not_eq)
 *)

Lemma eq_nat_inc :
  forall n m : nat, n <> m -> S n <> S m.
Proof.
  intros n m H eq. apply H.
  inversion eq as [ eq' ]. reflexivity.
Qed.

Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' ].
  (* m = 0 *)
    destruct n as [| n' ].
    (* n = 0 *) simpl. intros eqH eq. discriminate eqH.
    (* n = S n' *) simpl. intros eqH eq. discriminate eq.
  (* m = S m' *)
    destruct n as [| n' ].
    (* n = 0 *)
      simpl. intros eqH eq. discriminate eq.
    (* n = S n' *)
      simpl. intros eqH. apply eq_nat_inc.
      apply IHm'. exact eqH.
Qed.
(* ☐ *)


(* 存在量化子 *)

Inductive ex (X:Type) (P : X -> Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop :=
  ex nat ev.

Definition sine : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" :=
  (ex _ (fun x => p)) (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" :=
  (ex _ (fun x:X => p)) (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity. Qed.

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity. Qed.

Theorem exists_example_2 :
  forall n, (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm. Qed.

(*
練習問題: ★ (english_exists)

英語では、以下の命題は何を意味しているでしょうか？
      ex nat (fun n => ev (S n))

次の証明オブジェクトの定義を完成させなさい
 *)

Definition p : ex nat (fun n => ev (S n)) :=
  ex_intro _ (fun n => ev (S n)) 1 (ev_SS 0 ev_0).
(* ☐ *)

(*
練習問題: ★ (dist_not_exists)

"全ての x についてP が成り立つ" ということと " P を満たさない x は存在しない" というこ
とが等価であることを証明しなさい。
 *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P PH NH.
  inversion NH as [x NP].
  apply NP. apply PH.
Qed.
(* ☐ *)

(*
練習問題: ★★★, optional (not_exists_dist)

一方、古典論理の「排中律（law of the excluded middle）」が必要とされる場合もあります。
 *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros em X P NNP x.
  destruct (em (P x)) as [XP | NXP].
  (* P x *) exact XP.
  (* ~ P x *)
    apply ex_falso_quodlibet.
    apply NNP. exists x. exact NXP.
Qed.
(* ☐ *)

(*
練習問題: ★★ (dist_exists_or)

存在量化子が論理和において分配法則を満たすことを証明しなさい。
 *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.

  (* -> *)
  intros ePorQ. inversion ePorQ as [ x orH ].
  destruct orH as [ PX | QX ].
  (* P x *) left.  exists x. exact PX.
  (* Q x *) right. exists x. exact QX.

  (* <- *)
  intros EPorEQ.
  destruct EPorEQ as [ EP | EQ ].

  (* P x *)
  inversion EP as [ x PX ].
  exists x. left.  exact PX.

  (* Q x *)
  inversion EQ as [ x QX ].
  exists x. right. exact QX.
Qed.
(* ☐ *)


(* 等しいということ（同値性） *)

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.

Notation "x = y" :=
  (eq _ x y) (at level 70, no associativity) : type_scope.

Inductive eq' (X:Type) (x:X) : X -> Prop :=
  refl_equal' : eq' X x x.

Notation "x =' y" :=
  (eq' _ x y) (at level 70, no associativity) : type_scope.

(*
練習問題: ★★★, optional (two_defs_of_eq_coincide)

これら二つの定義が等価であることを確認しなさい。
 *)

Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
  x = y <-> x =' y.
Proof.
  intros X x y.
  split.

  (* -> *)
  intros eqH.
  inversion eqH as [ x' y' eqT ].
  apply refl_equal'.

  (* <- *)
  intros eqH.
  inversion eqH as [ eqT ].
  apply refl_equal.
Qed.
(* ☐ *)

Check eq'_ind.

Definition four : 2 + 2 = 1 + 3 :=
  refl_equal nat 4.
Definition singleton :
  forall (X:Set) (x:X), [] ++ [x] = x::[] :=
  fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.


(* Inversion 再び *)

(* 命題としての関係 *)

Module LeFirstTry.

Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall n m, (le n m) -> (le n (S m)).

End LeFirstTry.

Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  intros H. inversion H. inversion H1. Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
| nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
| ne_1 : ev (S n) -> next_even n (S n)
| ne_2 : ev (S (S n)) -> next_even n (S (S n)).


(*
練習問題: ★★, recommended (total_relation)

二つの自然数のペア同士の間に成り立つ帰納的な関係 total_relation を定義しなさ
い。
 *)

Lemma le_dec_R :
  forall {n m}, n <= S m -> n <= m \/ n = S m.
(* -> *)
Proof.
  intros n m H0.
  inversion H0 as [ eq | m' H1 eq ].
  (* le_n *) right. reflexivity.
  (* le_S *) left.  exact H1.
Qed.

Lemma le_dec_L :
  forall {n m}, n <= m \/ n = S m -> n <= S m.
(* <- *)
Proof.
  intros n m H.
  destruct H as [LE | EQ].
  (* le *) apply (le_S n m LE).
  (* eq *) rewrite <- EQ. apply le_n.
Qed.

Lemma le_dec :
  forall {n m}, n <= S m <-> n <= m \/ n = S m.
Proof.
  split. apply le_dec_R. apply le_dec_L.
Qed.

Lemma inc_le_trans :
  forall n m, n <= m <-> S n <= S m.
Proof.
  split.

  (* -> *)
  intros H.
  induction H as [ EQ | m' LE ].
  (* EQ *) apply le_n.
  (* LE *) apply le_S. apply IHLE.

  (* <- *)
    generalize dependent n.
    induction m as [| m'].
    (* m = 0 *)
      intros n H.
      inversion H as [eq | m' L].
      (* le_n *) apply le_n.
      (* le_S *) inversion L.

    (* m = S m' *)
      intros n H.
      destruct (le_dec_R H) as [ LE | EQ ].
      (* S n <= S m' *) apply le_S. apply IHm'. exact LE.
      (* S n = S (S m') *) inversion EQ as [ EQ1 ]. apply le_n.
Qed.

Lemma inc_le_trans_LR :
  forall n m, n <= m -> S n <= S m.
Proof.
  intros n m.
  destruct (inc_le_trans n m) as [ LR RL ].
  exact LR.
Qed.

Lemma inc_le_trans_RL :
  forall n m,  S n <= S m -> n <= m.
Proof.
  intros n m.
  destruct (inc_le_trans n m) as [ LR RL ].
  exact RL.
Qed.

Lemma logic_O_le_n :
  forall n, 0 <= n.
Proof.
  induction n as [| n'].
  apply le_n.
  apply le_S.
  apply IHn'.
Qed.

Inductive total_relation (R : nat -> nat -> Prop) (a b:nat) : Prop :=
  total_order : R a b \/ R b a -> total_relation R a b.

Theorem total_order_le :
  forall a b, total_relation le a b.
Proof.
  intros a b.
  apply total_order.
  generalize dependent b.
  induction a as [| a' IHa ].
  (* a = 0 *)
    intro b. left. induction b as [| b' IHb].
      (* b = 0 *)    apply le_n.
      (* b = S b' *) apply le_S. apply IHb.
  (* a = S a' *)
    intro b.
    destruct b as [| b'].
      (* b = 0 *)    right. apply logic_O_le_n.
      (* b = S b' *)
        destruct (IHa b') as [ ABH | BAH ]
        ; [ left | right ]
        ; apply inc_le_trans_LR
        ; [ (* a' <= b' *) exact ABH
          | (* b' <= a' *) exact BAH
          ].
Qed.
(* ☐ *)

(*
練習問題: ★★ (empty_relation)

自然数の間では決して成り立たない関係 empty_relation を帰納的に定義しなさい。
 *)

Inductive empty_relation (a b:nat) : Prop :=
  empty_relation_0 : S a = b /\ S b = a -> empty_relation a b.

(* ☐ *)

(*
練習問題: ★★★, recommended (R_provability)
 *)

Module R.

(*
次は三つや四つの値の間に成り立つ関係を同じように定義してみましょう。例えば、
次のような数値の三項関係が考えられます。

Inductive R : nat → nat → nat → Prop :=
   | c1 : R 0 0 0
   | c2 : ∀ m n o, R m n o → R (S m) n (S o)
   | c3 : ∀ m n o, R m n o → R m (S n) (S o)
   | c4 : ∀ m n o, R (S m) (S n) (S (S o)) → R m n o
   | c5 : ∀ m n o, R m n o → R n m o.
*)

Inductive R : nat -> nat -> nat -> Prop :=
| c1 : R 0 0 0
| c2 : forall m n o, R m n o -> R (S m) n (S o)
| c3 : forall m n o, R m n o -> R m (S n) (S o)
| c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
| c5 : forall m n o, R m n o -> R n m o.

(*
  * 次の命題のうち、この関係を満たすと証明できると言えるのはどれでしょうか。
      + R 1 1 2
      + R 2 2 6
 *)

(* R 1 1 2 *)
(* R 2 2 6 *)

(*
  * この関係 R の定義からコンストラクタ c5 を取り除くと、証明可能な命題の範囲
    はどのように変わるでしょうか？端的に（１文で）説明しなさい。
 *)
(*
  * この関係 R の定義からコンストラクタ c4 を取り除くと、証明可能な命題の範囲
    はどのように変わるでしょうか？端的に（１文で）説明しなさい。
 *)

(* ☐ *)

(*
練習問題: ★★★, optional (R_fact)

関係 R の、等値性に関する特性をあげ、それを証明しなさい。それは、もし R m n o
が true なら m についてどんなことが言えるでしょうか？ n や o についてはどうで
しょうか？その逆は？
 *)

Theorem m_plus_n_eq_o_left :
  forall m n o, R m n o -> m + n = o.
Proof.
  intros m n o H.
  induction H as [| m' n' o' H101 |  m' n' o' H011 |  m' n' o' H112 |  m' n' o' Hswap ].
  (* c1 *) reflexivity.
  (* c2 *) simpl. rewrite -> IHH101. reflexivity.
  (* c3 *) rewrite <- (plus_n_Sm m' n'). rewrite -> IHH011. reflexivity.
  (* c4 *)
    simpl in IHH112. rewrite <- (plus_n_Sm m' n') in IHH112.
    inversion IHH112. reflexivity.
  (* c5 *) rewrite -> plus_comm. apply IHHswap.
Qed.

Lemma m_plus_n_O' :
  forall m n, m + n = 0 -> m = 0.
Proof.
  destruct m as [| m'].
  (* m = 0 *) reflexivity.
  (* m = S m' *)
    intros n H.
    simpl in H. inversion H.
Qed.

Lemma m_plus_n_O :
  forall m n, m + n = 0 -> m = 0 /\ n = 0.
Proof.
  split.

  (* m = 0 *)
  apply (m_plus_n_O' m n).
  exact H.

  (* n = 0 *)
  rewrite -> (plus_comm m n) in H.
  apply (m_plus_n_O' n m).
  exact H.
Qed.

Theorem m_plus_n_eq_o_right :
  forall m n o, m + n = o -> R m n o.
Proof.
  intros m n o H.
  generalize dependent m.
  generalize dependent n.

  induction o as [| o'].
  (* o = 0 *)
    intros n m H.
    apply m_plus_n_O in H. inversion H.
    rewrite -> H0. rewrite -> H1.
    apply c1.

  (* o = S o' *)
    intros n m H.

    (* c2 *)
      destruct m as [| m'].
      (* m = 0*)
        destruct n as [| n'].
        (* n = 0 *) inversion H.
        (* n = S n'*)
        simpl in H. apply c3. apply (IHo' n' 0). inversion H. reflexivity.

      (* m = S m' *)
        apply c2. apply IHo'. simpl in H. inversion H. reflexivity.
Qed.


(* true なら -> 真なら *)

(* ☐ *)

End R.

(*
練習問題: ★★★, recommended (all_forallb)

リストに関する属性 all を定義しなさい。それは、型 X と属性 P : X → Prop をパ
ラメータとし、 all X P l が「リスト l の全ての要素が属性 P} を満たす」とする
ものです。
 *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| all_nil  : all X P []
| all_cons : forall x xs, P x -> all X P xs -> all X P (x :: xs)
.

(*
Poly.v の練習問題 forall_exists_challenge に出てきた関数 forallb を思い出して
みましょう。

Fixpoint forallb {X : Type} (test : X → bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.
 *)

(*
属性 all を使って関数 forallb の仕様を書き、それを満たすことを証明しなさい。
できるだけその仕様が厳格になるようにすること。

関数 forallb の重要な性質が、あなたの仕様から洩れている、ということはありませ
んか？
 *)

Theorem all_forallb :
  forall {X} (test : X -> bool) (xs : list X),
    forallb test xs = true <-> all X (fun x => test x = true) xs.
Proof.
  intros X test xs. split.

  (* -> *)
  induction xs as [| x xs'].
  (* [] *)  intros EQ. apply all_nil.
  (* x :: xs' *)
    simpl.
    intros EQ.
    destruct (test x) as [] eqn: TxH.
    (* true *)
      apply all_cons. apply TxH.
      apply IHxs'. apply EQ.
    (* false *) inversion EQ.

  (* <- *)
  induction xs as [| x xs'].
  (* [] *) reflexivity.
  (* x :: xs' *)
    intros H.
    inversion H as [| P AP].
    simpl. rewrite -> H2.
    apply IHxs'. apply H3.
Qed.

(* ☐ *)

(*
練習問題: ★★★★, optional (filter_challenge)

Coq の主な目的の一つは、プログラムが特定の仕様を満たしていることを証明するこ
とです。それがどういうことか、filter 関数の定義が仕様を満たすか証明してみまし
ょう。まず、その関数の仕様を非形式的に書き出してみます。

集合 X と関数 test: X→bool、リストl とその型 list X を想定する。さらに、l が
二つのリスト l1 と l2 が順序を維持したままマージされたもので、リスト l1 の要
素はすべて test を満たし、 l2 の要素はすべて満たさないとすると、filter test l
= l1 が成り立つ。

リスト l が l1 と l2 を順序を維持したままマージしたものである、とは、それが
l1 と l2 の要素をすべて含んでいて、しかも互いに入り組んではいても l1 、 l2 の
要素が同じ順序になっている、ということです。例えば、

    [1,4,6,2,3]

は、以下の二つを順序を維持したままマージしたものです。
    [1,6,2]

と、
    [4,3]

課題は、この仕様をCoq の定理の形に書き直し、それを証明することです。（ヒント
：まず、一つのりすとが二つのリストをマージしたものとなっている、ということを
示す定義を書く必要がありますが、これは帰納的な関係であって、 Fixpoint で書く
ようなものではありません。）
 *)

Inductive in_order_merge {X:Type} : list X -> list X -> list X -> Prop :=
| merge_nil : in_order_merge [] [] []
| merge_cons_L : forall (x:X) (l1 l2 l : list X),
                 in_order_merge l1 l2 l -> in_order_merge (x::l1) l2 (x::l)
| merge_cons_R : forall (x:X) (l1 l2 l : list X),
                 in_order_merge l1 l2 l -> in_order_merge l1 (x::l2) (x::l)
.

(*
集合 X と関数 test: X→bool、リストl とその型 list X を想定する。さらに、l が
二つのリスト l1 と l2 が順序を維持したままマージされたもので、リスト l1 の要
素はすべて test を満たし、 l2 の要素はすべて満たさないとすると、filter test l
= l1 が成り立つ。
 *)

Theorem filter_challenge :
  forall {X:Type} (test : X -> bool) (l l1 l2 : list X),
    in_order_merge l1 l2 l ->
    all X (fun x => test x = true) l1 ->
    all X (fun x => test x = false) l2 ->
    filter test l = l1.
Proof.
  intros X test.
  induction l as [| x xs] eqn: LEQ.
  (* [] *) intros l1 l2 M. inversion M. reflexivity.
  (* x :: xs*)
    intros l1 l2 M T F.
    inversion M as [| x0 xsL xsR xs0 ML | x0 xsL xsR xs0 MR].
    (* L *)
      (* subst x0 xs0 xsR. *)
      rewrite -> H2 in H.
      rewrite -> H.
      inversion T as [| x1 xs1 p T' ].
      (* all_nil *) rewrite <- H1 in H. inversion H.
      (* all_cons *)
        rewrite <- H1 in H.
        inversion H.
        simpl. rewrite -> p0.

    (* (* merge_nil *) reflexivity. *)
    (* merge_cons_L *)
    (*
      intros T F.

      simpl. rewrite -> H1.
      f_equal.
      apply (IHxs xl1).
     *)
    (* merge_cons_R *)
Admitted.
(* ☐ *)

(*
練習問題: ★★★★★, optional (filter_challenge_2)

filter の振る舞いに関する特性を別の切り口で表すとこうなります。「test の結果
が true なる要素だけでできた、リスト l のすべての部分リストの中で、filter
test l が最も長いリストである。」これを形式的に記述し、それを証明しなさい。
 *)
(* ☐ *)

(*
練習問題: ★★★★, optional (no_repeats)

次の、帰納的に定義された命題は、

Inductive appears_in {X:Type} (a:X) : list X → Prop :=
  | ai_here : ∀ l, appears_in a (a::l)
  | ai_later : ∀ b l, appears_in a l → appears_in a (b::l).

値 a がリスト l の要素として少なくとも一度は現れるということを言うための、精
確な方法を与えてくれます。

次の二つはappears_in に関するウォームアップ問題です。
 *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app :
  forall {X:Type} (xs ys : list X) (x:X),
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
Admitted.

Lemma app_appears_in :
  forall {X:Type} (xs ys : list X) (x:X),
    appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
Admitted.

(*
では、 appears_in を使って命題 disjoint X l1 l2 を定義してください。これは、
型 X の二つのリスト l1 、 l2 が共通の要素を持たない場合にのみ証明可能な命題で
す。

次は、 appears_in を使って帰納的な命題 no_repeats X l を定義してください。こ
れは, 型 X のリスト l の中のどの要素も、他の要素と異なっている場合のみ証明で
きるような命題です。例えば、 no_repeats nat [1,2,3,4] や no_repeats bool []
は証明可能ですが、 no_repeats nat [1,2,1] や no_repeats bool [true,true] は証
明できないようなものです。

最後に、disjoint、 no_repeats、 ++ （リストの結合）の三つを使った、何か面白い
定理を考えて、それを証明してください。
 *)

(* ☐ *)

(* 少し脱線: <= と < についてのさらなる事実 *)

(* 練習問題: ★★, optional (le_exercises) *)

Theorem O_le_n :
  forall n, 0 <= n.
Proof.
  induction n as [| n'].
  apply le_n.
  apply le_S.
  apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm :
  forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [EQ | m' LE].
  (* EQ *) apply le_n.
  (* LE *) apply le_S. apply IHLE.
Qed.

Theorem Sn_le_Sm__n_le_m :
  forall n m, S n <= S m -> n <= m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m'].
  (* m = 0 *)
    intros n H.
    inversion H as [eq | m' L].
    (* le_n *) apply le_n.
    (* le_S *) inversion L.

  (* m = S m' *)
    intros n H.
    destruct (le_dec_R H) as [LE | EQ].
    (* S n <= S m' *) apply le_S. apply IHm'. apply LE.
    (* S n = S (S m') *) inversion EQ as [ EQ1 ]. apply le_n.
Qed.

Theorem le_plus_l :
  forall a b, a <= a + b.
Proof.
  induction a as [| a'].
  (* a = 0 *) apply O_le_n.
  intro b.
  rewrite <- (plus_1_l a').
  rewrite <- (plus_assoc 1 a' b).
  simpl.
  apply n_le_m__Sn_le_Sm.
  apply IHa'.
Qed.

Theorem plus_lt :
  forall n1 n2 m,
    n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m.
  generalize dependent n2.
  generalize dependent n1.
  induction m as [| m'].
  (* m = 0 *) intros n1 n2 H. inversion H.
  (* m = S m' *)
    intros n1 n2 H.
    apply le_dec_R in H.
    destruct H as [LE | EQ].
    (* LE *)
    apply IHm' in LE.
    inversion LE as [n1H n2H].
    split.
      apply le_S. apply n1H.
      apply le_S. apply n2H.

    (* EQ *)
    rewrite <- EQ.
    split.
      apply n_le_m__Sn_le_Sm. apply le_plus_l.
      apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
Qed.

Theorem lt_S :
  forall n m, n < m -> n < S m.
Proof.
  intros n m H. apply le_S. apply H.
Qed.

Theorem ble_nat_true :
  forall n m, ble_nat n m = true -> n <= m.
Proof.
  induction n as [| n'].
  (* n = 0 *) intros m H. apply O_le_n.
  (* n = S n' *)
    destruct m as [| m'].
    (* m = 0 *) intros H. inversion H.
    (* m = S m' *)
      simpl. intros H.
      apply n_le_m__Sn_le_Sm. apply IHn'.  apply H.
Qed.

Theorem ble_nat_n_Sn_false :
  forall n m,
    ble_nat n (S m) = false ->
    ble_nat n m = false.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  (* m = 0 *)
    destruct n as [| n'].
    (* n = 0 *) simpl. intro H. inversion H.
    (* n = S n' *) simpl. intro H. reflexivity.

  (* m = S m' *)
    intros n H.
    destruct n as [| n'].
    (* n = 0 *) simpl in H. inversion H.
    (* n = S n' *)
      simpl. apply IHm'.
      simpl in H. apply H.
Qed.

Theorem ble_nat_false :
  forall n m,
    ble_nat n m = false -> ~(n <= m).
Proof.
  induction n as [| n'].
  (* n = 0 *)
    destruct m as [| m'].
    (* 0 *)   simpl. intro H. inversion H.
    (* S m'*) simpl. intro H. inversion H.
  (* n = S n' *)
    intros m H.
    destruct m as [| m'].
    (* 0 *) intro LE. inversion LE.
    (* S m' *)
      simpl in H.
      intro LE.
      apply Sn_le_Sm__n_le_m in LE.
      apply (IHn' m').
      apply H. apply LE.
Qed.
(* ☐ *)


(* 練習問題: ★★★, recommended (nostutter) *)

(*
述語の帰納的な定義を定式化できるようになるというのは、これから先の学習に必要なスキ
ルになってきます。

この練習問題は、何の力も借りず自力で解いてください。もし誰かの力を借りてしまった場
合は、そのことをコメントに書いておいてください。

同じ数値が連続して現れるリストを "stutters" （どもったリスト）と呼ぶことにします。
述語 "nostutter mylist" は、 mylist が「どもったリスト」でないことを意味しています
。nostutter の帰納的な定義を記述しなさい。（これは以前の練習問題に出てきた
no_repeats という述語とは異なるものです。リスト 1,4,1 は repeats ではありますが
stutter ではありません。）
 *)

Inductive nostutter: list nat -> Prop :=

.

(*
できた定義が、以下のテストを通過することを確認してください。通過できないものがあっ
たら、定義を修正してもかまいません。あなたの書いた定義が、正しくはあるけれど私の用
意した模範解答と異なっているかもしれません。その場合、このテストを通過するために別
の証明を用意する必要があります。

以下の Example にコメントとして提示された証明には、色々な種類の nostutter の定義に
対応できるようにするため、まだ説明していないタクティックがいくつか使用されています
。まずこれらのコメントをはずしただけの状態で確認できればいいのですが、もしそうした
いなら、これらの証明をもっと基本的なタクティックで書き換えて証明してもかまいません
。
 *)

Example test_nostutter_1: nostutter [3,1,4,1,5,6].
Admitted.

Example test_nostutter_2: nostutter [].
Admitted.

Example test_nostutter_3: nostutter [5].
Admitted.

Example test_nostutter_4: not (nostutter [3,1,1,4]).
Admitted.
(* ☐ *)

(* 練習問題: ★★★★, optional (pigeonhole principle) *)

(*
「鳩の巣定理（ "pigeonhole principle" ）」は、「数えるあげる」ということについての
基本的な事実を提示しています。「もし n 個の鳩の巣に n 個より多い数のものを入れよう
とするなら、どのような入れ方をしてもいくつかの鳩の巣には必ず一つ以上のものが入るこ
とになる。」というもので、この、数値に関する見るからに自明な事実を証明するにも、な
かなか自明とは言えない手段が必要になります。我々は既にそれを知っているのですが...

まず、補題を二つほど証明しておきます。（既に数値のリストについては証明済みのもので
すが、任意のリストについてはのものはまだないので）
 *)

Lemma app_length :
  forall {X:Type} (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
Admitted.

Lemma appears_in_app_split :
  forall {X:Type} (x:X) (l:list X),
    appears_in x l ->
    exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
Admitted.

(*
そして、述語 repeats の定義をします（以前の練習問題 no_repeats に類似したものです
）。それは repeats X l が、「 l の中に少なくとも一組の同じ要素（型 X の）を含む」
という主張となるようなものです。
 *)

Inductive repeats {X:Type} : list X -> Prop :=

.

(*
この「鳩の巣定理」を定式化する方法を一つ挙げておきましょう。リスト l2 が鳩の巣に貼
られたラベルの一覧を、リスト l1 はそのラベルの、アイテムへの割り当ての一覧を表して
いるとします。もしラベルよりも沢山のアイテムがあったならば、少なくとも二つのアイテ
ムに同じラベルが貼られていることになります。おそらくこの証明には「排中律（
excluded_middle ）」が必要になるでしょう。
 *)

Theorem pigeonhole_principle:
  forall {X:Type} (l1 l2:list X),
    excluded_middle ->
    (forall x, appears_in x l1 -> appears_in x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof. intros X l1. induction l1.
Admitted.
(* ☐ *)

(* 選択課題 *)

(* ∧ や ∨ のための帰納法の原理 *)

(* 練習問題: ★ (and_ind_principle) *)

(*
連言（ conjunction ）についての帰納法の原理を予想して、確認しなさい。
 *)

(* ☐ *)

(* 練習問題: ★ (or_ind_principle) *)

(*
選言（ disjunction ）についての帰納法の原理を予想して、確認しなさい。
 *)

(* ☐ *)

Check and_ind.


Inductive or' (P Q : Prop) : Prop :=
| or'_introl : P -> or' P Q
| or'_intror : Q -> or' P Q
.

Check or'_ind.

Definition nrect :=
fun (P : nat -> Type) (f : P 0)
    (f0 : forall n : nat, P n -> P(S n)) =>
  fix F (n : nat) : P n :=
  match n return (P n) with
    | 0 => f
    | S n0 => f0 n0 (F n0)
  end.

(* 帰納法のための明白な証明オブジェクト *)
