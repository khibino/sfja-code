
(* 型システム *)

Require Export Smallstep.

(* さらに自動化 *)

(* auto と eauto タクティック *)

Lemma auto_example_1 :
  forall P Q R S T U : Prop,
    (P -> Q) ->
    (P -> R) ->
    (T -> R) ->
    (S -> T -> U) ->
    ((P->Q) -> (P->S)) ->
    T ->
    P ->
    U.
Proof. auto. Qed.

Lemma auto_example_2 :
  forall P Q R : Prop,
    Q ->
    (Q -> R) ->
    P \/ (Q /\ R).
Proof.
  auto. Qed.

Lemma auto_example_2a :
  forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto using conj, or_introl, or_intror. Qed.

(* Hint Resolve l. *)
(* Hint Constructors c. *)
(* Hint Unfold d. *)

Hint Constructors refl_step_closure.
Hint Resolve beq_id_eq beq_id_false_not_eq.

(* Proof with タクティック *)
(* solve by inversion タクティック *)
(* try solve タクティック *)

(* f_equal タクティック *)
(* normalize タクティック *)

Definition astep_many st := refl_step_closure (astep st).
Notation " t '/' st '==>a*' t' " := (astep_many st t t')
  (at level 40, st at level 39).

Example astep_example1 :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  apply rsc_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2.
      apply av_num.
      apply AS_Mult.
  apply rsc_step with (ANum 15).
    apply AS_Plus.
  apply rsc_refl.
Qed.

Hint Constructors astep aval.
Example astep_example1' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  eapply rsc_step. auto. simpl.
  eapply rsc_step. auto. simpl.
  apply rsc_refl.
Qed.

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
   repeat (print_goal; eapply rsc_step ;
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply rsc_refl.

Example astep_example1'' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  normalize.
Qed.

Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

(* 型付きの算術式 *)

(* 構文 *)

Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_iszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue tm_true
  | bv_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tm_zero
  | nv_succ : forall t, nvalue t -> nvalue (tm_succ t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.

(* スモールステップ簡約 *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tm_succ t1) ==> (tm_succ t1')
  | ST_PredZero :
      (tm_pred tm_zero) ==> tm_zero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tm_pred (tm_succ t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tm_pred t1) ==> (tm_pred t1')
  | ST_IszeroZero :
      (tm_iszero tm_zero) ==> tm_true
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tm_iszero (tm_succ t1)) ==> tm_false
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tm_iszero t1) ==> (tm_iszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred"
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.

(* 正規形と値 *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(* 練習問題: ★★, optional (some_tm_is_stuck) *)

Example some_tm_is_stuck :
  exists t, stuck t.
Proof.
  exists (tm_succ tm_true).
  split.

  + intro E.
    destruct E as [s S].
    solve by inversion 2.

  + intro V.
    solve by inversion 3.
Qed.

(* ☐ *)


(* 練習問題: ★★★, optional (value_is_nf) *)

(*
ヒント: 証明中で、数値であることがわかっている項に対して帰納的推論をしなければなら
ないことになります。この帰納法は、その項自体にして適用することもできますし、その項
が数値であるという事実に対して適用することもできます。どちらでも証明は進められます
が、片方はもう片方よりもかなり短かくなります。練習として、ふたつの方法両方で証明を
完成させなさい。
 *)

Lemma value_is_nf :
  forall t, value t -> step_normal_form t.
Proof.
  intros t v.
  destruct v as [ B | N ].
  + intros [ rf RH ].
    inversion B; subst; inversion RH.
  + induction N as [ | t' N' ].
    - intros [ rf RH ].
      inversion RH.
    - intros [ rf RH ].
      apply IHN'.
      inversion RH; subst.
      exists t1'.
      assumption.
Qed.

Lemma value_is_nf_nat :
  forall t, value t -> step_normal_form t.
Proof.
  Admitted.

(* ☐ *)


(* 練習問題: ★★★, optional (step_deterministic) *)

(* value_is_nf を使うと、 step 関係もまた決定的であることが示せます。 *)

Theorem step_deterministic:
  partial_function step.
Proof with eauto.
Admitted.

(* ☐ *)

(* 型付け *)

Inductive ty : Type :=
  | ty_Bool : ty
  | ty_Nat : ty.


Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       has_type tm_true ty_Bool
  | T_False :
       has_type tm_false ty_Bool
  | T_If : forall t1 t2 t3 T,
       has_type t1 ty_Bool ->
       has_type t2 T ->
       has_type t3 T ->
       has_type (tm_if t1 t2 t3) T
  | T_Zero :
       has_type tm_zero ty_Nat
  | T_Succ : forall t1,
       has_type t1 ty_Nat ->
       has_type (tm_succ t1) ty_Nat
  | T_Pred : forall t1,
       has_type t1 ty_Nat ->
       has_type (tm_pred t1) ty_Nat
  | T_Iszero : forall t1,
       has_type t1 ty_Nat ->
       has_type (tm_iszero t1) ty_Bool.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

(* 例 *)

Example has_type_1 :
  has_type (tm_if tm_false tm_zero (tm_succ tm_zero)) ty_Nat.
Proof.
  apply T_If.
    apply T_False.
    apply T_Zero.
    apply T_Succ.
      apply T_Zero.
Qed.


Example has_type_not :
  ~ has_type (tm_if tm_false tm_zero tm_true) ty_Bool.
Proof.
  intros Contra. solve by inversion 2. Qed.

(* 練習問題: ★ (succ_hastype_nat__hastype_nat) *)

Example succ_hastype_nat__hastype_nat : forall t,
  has_type (tm_succ t) ty_Nat ->
  has_type t ty_Nat.
Proof.
Admitted.

(* ☐ *)

(* 進行 *)

(* 練習問題: ★★★, recommended (finish_progress_informal) *)

(* 次の証明を完成させなさい。 *)

(*
定理: ⊢ t : T であれば、 t は値であるか、さもなければある t' に対して t ⇑ t' である。
 *)

(*
証明: ⊢ t : T の導出に関する帰納法で証明する。

  * 導出で直前に適用した規則が T_If である場合、 t = if t1 then t2 else t3 かつ、
    ⊢ t1 : Bool、 ⊢ t2 : T かつ ⊢ t3 : T である。帰納法の仮定から、 t1 が値である
    か、さもなければ t1 が何らかの t1' に簡約できる。

      + t1 が値のとき、 t1 は nvalue か bvalue である。だが、 ⊢ t1 : Bool かつ、
        nvalue なる項に Bool 型を割り当てる規則はないため、 t1 は nvalue ではない
        。したがって、 t1 は bvalue である。すなわち、 true または false である。
        t1 = true のとき、 ST_IfTrue より t は t2 に簡約され、 t1 = false のときは
        ST_IfFalse から t は t3 に簡約される。どちらの場合も t の簡約は進められる
        。これが示そうとしていたことである。

      + t1 自体が ST_If で簡約できるとき、 t もまた簡約できる。
 *)

(* ☐ *)

(* 練習問題: ★★★ (finish_progress) *)

Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  Case "T_If".
    right. destruct IHHT1.
    SCase "t1 is a value". destruct H.
      SSCase "t1 is a bvalue". destruct H.
        SSSCase "t1 is tm_true".
          exists t2...
        SSSCase "t1 is tm_false".
          exists t3...
      SSCase "t1 is an nvalue".
        solve by inversion 2.     SCase "t1 can take a step".
      destruct H as [t1' H1].
      exists (tm_if t1' t2 t3)...
Admitted.

(* ☐ *)

(* 練習問題: ★ (step_review) *)

(*
おさらい: 「はい」か「いいえ」（true か false）で答えなさい。（提出の必要はありま
せん。）
 *)

(*
  * この言語では、型のついた正規形はすべて値である。

  * 値はすべて正規形である。

  * ワンステップ評価関係は全域関数である。
  *)

(* ☐ *)

(* 型保存 *)

(* 練習問題: ★★★, recommended (finish_preservation_informal) *)

(*
以下の証明を完成させなさい。

定理: ⊢ t : T かつ t ⇑ t' ならば ⊢ t' : T

証明: ⊢ t : T の導出に関する帰納法で証明する。

  * 導出で直前に使った規則が T_If の場合、 t = if t1 then t2 else t3、かつ ⊢ t1 :
    Bool、 ⊢ t2 : T かつ ⊢ t3 : T である。

    t が if ... の形式であることとスモールステップ簡約関係を見ると、 t ⇑ t' を示す
    ために使えるのは ST_IfTrue、 ST_IfFalse または ST_If のみである。

      + 直前の規則が ST_IfTrue の場合、 t' = t2 である。 ⊢ t2 : T であるのでこれは
        求める結果である。

      + 直前の規則が ST_IfFalse の場合、 t' = t3 である。 ⊢ t3 : T であるのでこれ
        は求める結果である。

      + 直前の規則が ST_If の場合、 t' = if t1' then t2 else t3' である。ここで、
        t1 ⇑ t1' である。 ⊢ t1 : Bool であるので、帰納法の仮定から ⊢ t1' : Bool で
        ある。また、 T_If 規則から ⊢ if t1' then t2 else t3 : T であり、これは求め
        る結果である。
 *)

(* ☐ *)

(* 練習問題: ★★ (finish_preservation) *)

Theorem preservation : forall t t' T,
  has_type t T ->
  t ==> t' ->
  has_type t' T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case;

         intros t' HE;

         try (solve by inversion).
    Case "T_If". inversion HE; subst.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
Admitted.

(* ☐ *)

(* 練習問題: ★★★ (preservation_alternate_proof) *)

(*
さらに、同一の性質を型付けの導出ではなく、評価の導出に関する帰納法で証明しなさい。
先ほどの証明の最初数行を注意深く読んで考え、各行が何をしているのか理解することから
始めましょう。この証明でも設定はよく似ていますが、まったく同じというわけではありま
せん。
 *)

Theorem preservation' : forall t t' T,
  has_type t T ->
  t ==> t' ->
  has_type t' T.
Proof with eauto.
Admitted.

(* ☐ *)

(* 型の健全性 *)

Definition stepmany := (refl_step_closure step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  has_type t T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP. apply (preservation x y T HT H).
  unfold stuck. split; auto. Qed.

(* 追加演習 *)

(* 練習問題: ★, recommended (subject_expansion) *)

(*
主部簡約性が成り立つのなら、その逆の性質、主部展開（subject expansion）性も成り立
つかどうか考えるのが合理的でしょう。すなわち、 t ⇑ t' かつ has_type t' T ならば
has_type t T は常に成り立つでしょうか。そうだと思うのなら、証明しなさい。そうでな
いと思うのなら、反例を挙げなさい。
 *)

(* ☐ *)

(* 練習問題: ★★ (variation1) *)

(*
評価関係に次のふたつの規則を追加したとします。
      | ST_PredTrue :
           (tm_pred tm_true) ⇑ (tm_pred tm_false)
      | ST_PredFalse :
           (tm_pred tm_false) ⇑ (tm_pred tm_true)

以下の性質のうち、この規則を追加しても依然として真であるのはどれでしょう。それぞれ
について、「真のままである」か「偽になる」かを書きなさい。偽になる場合には反例を挙
げなさい。

  * step の決定性

  * 型のつく項に対する step の正規化

  * 進行

  * 型保存
 *)

(* ☐ *)

(* 練習問題: ★★ (variation2) *)

(*
先程の問題とは別に、次の規則を型付け関係に追加したとしましょう。
      | T_IfFunny : ∀ t2 t3,
           has_type t2 ty_Nat →
           has_type (tm_if tm_true t2 t3) ty_Nat

以下のうち、この規則を追加しても依然として真であるのはどれでしょう。（上と同じスタ
イルで答えなさい。）

  * step の決定性

  * 型のつく項に対する step の正規化

  * 進行

  * 型保存
 *)

(* ☐ *)

(* 練習問題: ★★ (variation3) *)

(*
先程の問題とは別に、次の規則を型付け関係に追加したとしましょう。
      | T_SuccBool : ∀ t,
           has_type t ty_Bool →
           has_type (tm_succ t) ty_Bool

以下のうち、この規則を追加しても依然として真であるのはどれでしょう。（上と同じスタ
イルで答えなさい。）

  * step の決定性

  * 型のつく項に対する step の正規化

  * 進行

  * 型保存
 *)

(* ☐ *)

(* 練習問題: ★★ (variation4) *)

(*
先程の問題とは別に、次の規則を step 関係に追加したとしましょう。
      | ST_Funny1 : ∀ t2 t3,
           (tm_if tm_true t2 t3) ⇑ t3

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについて
それぞれ反例を挙げなさい。
 *)

(* ☐ *)

(* 練習問題: ★★ (variation5) *)

(*
先程の問題とは別に、次の規則を追加したとしましょう。
      | ST_Funny2 : ∀ t1 t2 t2' t3,
           t2 ⇑ t2' →
           (tm_if t1 t2 t3) ⇑ (tm_if t1 t2' t3)

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについて
それぞれ反例を挙げなさい。
 *)

(* ☐ *)

(* 練習問題: ★★ (variation6) *)

(*
先程の問題とは別に、次の規則を追加したとしましょう。
      | ST_Funny3 :
          (tm_pred tm_false) ⇑ (tm_pred (tm_pred tm_false))

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについて
それぞれ反例を挙げなさい。
 *)

(* ☐ *)

(* 練習問題: ★★ (variation7) *)

(*
先程の問題とは別に、次の規則を追加したとしましょう。
      | T_Funny4 :
            has_type tm_zero ty_Bool

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについて
それぞれ反例を挙げなさい。
 *)

(* ☐ *)

(* 練習問題: ★★ (variation8) *)

(*
先程の問題とは別に、次の規則を追加したとしましょう。
      | T_Funny5 :
            has_type (tm_pred tm_zero) ty_Bool

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについて
それぞれ反例を挙げなさい。
 *)

(* ☐ *)

(* 練習問題: ★★★, optional (more_variations) *)

(*
上の問題と同様の練習問題を自分で作りなさい。さらに、上の性質を選択的に成り立たなく
する方法、すなわち、上の性質のうちひとつだけを成り立たなるするよう定義を変更する方
法を探しなさい。
 *)
(* ☐ *)

(* 練習問題: ★ (remove_predzero) *)

(*
E_PredZero には少し直感に反するところがあります。 0 の前者を 0 と定義するよりは、
未定義とした方が意味があるように感じられるでしょう。これは step の定義から
E_PredZero を取り除くだけで実現できるでしょうか？
 *)

(* ☐ *)

(* 練習問題: ★★★★, optional (prog_pres_bigstep) *)

(*
評価関係をビッグステップスタイルで定義したとしましょう。その場合、進行と型保存性に
当たるものとしては何が適切でしょうか。
 *)

(* ☐ *)
