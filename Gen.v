
Require Export Poly.

Theorem double_injecitve_FAILED :
  forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
      Admitted.

Theorem double_injecitve' :
  forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    intros m eq.
    destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".
      assert (n' = m') as H.
      SSCase "Proof of assertion". apply IHn'.
        inversion eq. reflexivity.
      rewrite -> H. reflexivity. Qed.

Theorem double_injecitve_take2_FAILED :
  forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
Admitted.

Theorem double_injecitve_take2 :
  forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
        apply IHm'. inversion eq. reflexivity.
      rewrite -> H. reflexivity. Qed.


(*
練習問題: ★★★ (gen_dep_practice)

mに関する帰納法で以下を示しなさい。
 *)

Theorem plus_n_n_injective_take2 :
  forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n m H.
  generalize dependent n.
  induction m as [| m'].
  (* m = 0 *) destruct n as [| n'].
    (* n = 0 *) reflexivity.
    (* n = S n' *)
      intros eq. inversion eq.
  (* m = S m' *) destruct n as [| n'].
    (* n = 0 *) intros eq. inversion eq.
    (* n = S n' *)
      intros eq. inversion eq.
      rewrite <- plus_n_Sm in H0. rewrite <- plus_n_Sm in H0.
      inversion H0.
      rewrite <- (IHm' n' H1).
      reflexivity.
Qed.

(* lに関する帰納法で示しなさい。 *)

Theorem index_after_last:
  forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    index (S n) l = None.
Proof.
  intros n X l. generalize dependent n.
  induction l as [| x l'].
  (* l = [] *)
    destruct n as [| n'].
    (* n = O *) reflexivity.
    (* n = S n' *)
      intros eq. inversion eq.
  (* l = x :: l' *)
    destruct n as [| n'].
    (* n = O *)
      intros eq. inversion eq.
    (* n = S n' *)
      intros eq. inversion eq.
      rewrite -> H0.
      apply (IHl' n' H0).
Qed.
(* ☐ *)

(*
練習問題: ★★★, optional (index_after_last_informal)

index_after_lastのCoqによる証明に対応する非形式的な証明を書きな
さい。

Theorem: すべてのSet X, リスト l : list X, 自然数nに対して、
length l = n ならば index (S n) l = None。
 *)

(*
Proof:
  任意のリスト l について、帰納法を適用する
    l が [] のとき、
      さらに n が O のときは
        length [] = O -> @index X (S O) [] = None
          となり成立する。

      さらに n が S n' のときは
        length [] = S n' -> @index X (S n') [] = None
          これは前提が成立しないので成立する。
    l が x :: l' であり、
      forall n, length l' = n -> @index X (S n) l' = None
      が帰納法の仮定で成立しているとする

      さらに n が O のときは
        length (x :: l') = O -> @index X (S O) (x :: l') = None
          これは前提が成立しないので成立する。
      さらに n が S n' のときは
        length (x :: l') = S n' -> @index X (S (S n')) (x :: l') = None
          前提を length の定義で置き換え、
          結果を index  の定義で置き換えると、
        length l' = n' -> @index X (S n') l' = None
          これは帰納法の仮定から成立する。
☐
 *)

(*
練習問題: ★★★, optional (gen_dep_practice_opt)

lに関する帰納法で示しなさい。
 *)

Theorem length_snoc''' :
  forall (n : nat) (X : Type) (v : X) (l : list X),
    length l = n ->
    length (snoc l v) = S n.
Proof.
  intros n X v l. generalize dependent n.
  induction l as [|x l'].
  (* l = [] *)
    intros n eq. simpl in eq. rewrite <- eq.
    reflexivity.
  (* l = x :: l' *)
    simpl.
    destruct n as [| n'].
    (* n = O *) intros eq. inversion eq.
    (* n = S n' *)
      intros eq. inversion eq.
      rewrite -> (IHl' n' H0). rewrite -> H0.
      reflexivity.
Qed.
(* ☐ *)

(*
練習問題: ★★★, optional (app_length_cons)

app_lengthを使わずにl1に関する帰納法で示しなさい。
 *)

Theorem app_length_cons :
  forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n ->
    S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x n. generalize dependent n.
  induction l1 as [| x1 l1'].
  (* l1 = [] *)
    simpl. intros n eq. apply eq.
  (* l1 = x1 :: l1' *)
     destruct n as [| n'].
     (* n = O *) intros eq. inversion eq.
     (* n = S n' *)
       simpl. intros eq. inversion eq.
       rewrite -> (IHl1' n' H0). rewrite -> H0.
       reflexivity.
Qed.
(* ☐ *)

(*
練習問題: ★★★★, optional (app_length_twice)

app_lengthを使わずにl1に関する帰納法で示しなさい。
 *)

Lemma app_length_cons_eq :
  forall (X : Type) (l1 l2 : list X) (x : X),
    length (l1 ++ (x :: l2)) = S (length (l1 ++ l2)).
Proof.
  intros.
  induction l1 as [| x' l1'].
  (* l1 = [] *) reflexivity.
  (* l1 = x' :: l1' *)
    simpl. rewrite <- IHl1'.
    reflexivity.
Qed.

Theorem app_length_twice :
  forall (X:Type) (n:nat) (l:list X),
    length l = n ->
    length (l ++ l) = n + n.
Proof.
  intros X n l. generalize dependent n.
  induction l as [| x l'].
  (* l = [] *)
    simpl. intros n eq. rewrite <- eq.
    reflexivity.
  (* l = x :: l' *)
    intros n eq.
    destruct n as [| n'].
    (* n = O *) inversion eq.
    (* n = S n' *)
      inversion eq.
      rewrite -> H0.
      simpl.
      rewrite <- plus_n_Sm.
      rewrite -> app_length_cons_eq.
      rewrite -> (IHl' n' H0).
      reflexivity.
Qed.
(* ☐ *)
