
Require Export Basics.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
    | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
    | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3, 4)).

Definition fst' (p : natprod) : nat :=
  match p with
    | (x, y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
    | (x, y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x, y) => (y, x)
  end.

Theorem surjective_pairing' :
  forall (n m : nat), (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck :
  forall (p : natprod), p = (fst p, snd p).
Proof.
  simpl. Admitted.

Theorem surjective_pairing :
  forall (p : natprod), p = (fst p, snd p).
Proof.
  intros p. destruct p as (n, m). simpl. reflexivity. Qed.


(* 練習問題: ★ (snd_fst_is_swap) *)

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as (n, m). simpl. reflexivity. Qed.
(* ☐ *)

Inductive natlist : Type :=
| nil  : natlist
| cons : nat -> natlist -> natlist.

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition l_123' := 1 :: (2 :: (3 :: nil)).
Definition l_123'0 := 1 :: (2 :: (3 :: [ ])).
Definition l_123'' := 1 :: 2 :: 3 :: nil.
Definition l_123''' := [1,2,3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil
    | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.
Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
    | nil => default
    | h :: t => h
  end.

Definition tail (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => t
  end.

Example test_hd1: hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tail: tail [1,2,3] = [2,3].
Proof. reflexivity. Qed.

(*
練習問題: ★★, recommended (list_funs)

以下の nonzeros、 oddmembers、 countoddmembers の定義を完成させなさい。
 *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | O :: xs => nonzeros xs
    | x :: xs => x :: nonzeros xs
    | [ ]     => []
  end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
    | x :: xs =>
        match oddb x with
          | true  => x :: oddmembers xs
          | false => oddmembers xs
        end
    | [ ]     => [ ]
  end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
    | x :: xs =>
        match oddb x with
          | true  => S (countoddmembers xs)
          | false => countoddmembers xs
        end
    | [ ]     => O
  end.

Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

(* ☐ *)

(*
練習問題: ★★ (alternate)

alternate の定義を完成させなさい。この関数は、ふたつのリストから交互に要素を取り
出しひとつに「綴じ合わせる」関数です。具体的な例は下のテストを見てください。

注意: alternate の自然な定義のひとつは、「Fixpoint による定義は『明らかに停止する
』ものでなければならない」という Coq の要求を満たすことができません。このパターン
にはまってしまったようであれば、両方のリストの要素を同時に見ていくような少し冗長
な方法を探してみてください。
 *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | x :: xs, y :: ys => x :: y :: alternate xs ys
    | x :: xs, [ ]     => l1
    | [ ],     _       => l2
  end.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20,30] = [20,30].
Proof. reflexivity. Qed.

(* ☐ *)

Definition bag := natlist.

(*
練習問題: ★★★ (bag_functions)

バッグに対する count、 sum、 add、 member 関数の定義を完成させなさい。
 *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
    | [ ] => 0
    | x :: xs =>
        match (beq_nat x v) with
          | true  => 1 + count v xs
          | false => count v xs
        end
  end.

(* 下の証明はすべて reflexivity だけでできます。 *)

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof. reflexivity. Qed.


(*
多重集合の sum （直和。または非交和）は集合の union （和）と同じようなものです。
sum a b は a と b の両方の要素を持つ多重集合です。（数学者は通常、多重集合の
union にもう少し異なる定義を与えます。それが、この関数の名前を union にしなかった
理由です。） sum のヘッダには引数の名前を与えませんでした。さらに、 Fixpoint では
なく Definition を使っています。ですから、引数に名前がついていたとしても再帰的な
処理はできません。問題をこのように設定したのは、 sum を（定義済みの関数を使うとい
った）別の方法で定義できないか考えさせるためです。
 *)

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1,4,1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  ble_nat 1 (count v s).

Example test_member1: member 1 [1,4,1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1,4,1] = false.
Proof. reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★★, optional (bag_more_functions)

練習として、さらにいくつかの関数を作成してください。
 *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    | [ ] => [ ]
    | x :: xs =>
        match (beq_nat x v) with
          | true  => xs
          | false => x :: remove_one v xs
        end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | [ ] => [ ]
    | x :: xs =>
        match (beq_nat x v) with
          | true  => remove_all v xs
          | false => x :: remove_all v xs
        end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | [ ] => true
    | e :: es =>
        match member e s2 with
          | true  => subset es (remove_one e s2)
          | false => false
        end
  end.

Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
Proof. reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★★, recommended (bag_theorem)

count や add を使ったバッグに関する面白い定理書き、それを証明しなさい。この問題は
いわゆる自由課題で、真になることがわかっていても、証明にはまだ習っていない技を使
わなければならない定理を思いついてしまうこともあります。証明に行き詰まってしまっ
たら気軽に質問してください。
 *)

Theorem count_add_bag :
  forall (v : nat) (s : bag), count v (add v s) = 1 + count v s.
Proof.
  intros v s. simpl. rewrite <- beq_nat_refl. reflexivity. Qed.

Theorem count_sum_bag :
  forall (v : nat) (xs ys : bag), count v (sum xs ys) = count v xs + count v ys.
Proof.
  intros v xs ys. induction xs as [| x xs'].
  Case "xs = [ ]". reflexivity.
  Case "xs = x :: xs'".
    simpl. rewrite -> IHxs'. destruct (beq_nat x v).
    reflexivity. reflexivity. Qed.

(* ☐ *)


Theorem nil_app :
  forall l:natlist, [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred :
  forall l:natlist, pred (length l) = length (tail l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity. Qed.

Theorem app_ass :
  forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_length :
  forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
    | nil => [v]
    | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry :
  forall l : natlist, length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl. Admitted.

Theorem length_snoc :
  forall n : nat, forall l : natlist,
    length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_length :
  forall l : natlist, length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    simpl. rewrite -> length_snoc.
    rewrite -> IHl'. reflexivity. Qed.


(*
リストについての練習問題 (1)

練習問題: ★★★, recommended (list_exercises)

リストについてさらに練習しましょう。
 *)

Theorem app_nil_end :
  forall l : natlist, l ++ [] = l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil". reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl'. reflexivity. Qed.

Lemma rev_snoc :
  forall (l : natlist) (n : nat), rev (snoc l n) = n :: rev l.
Proof.
  intros l n. induction l as [| m l'].
  Case "l = nil". reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl'.
    simpl. reflexivity. Qed.

Theorem rev_involutive :
  forall l : natlist, rev (rev l) = l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil". reflexivity.
  Case "l = cons".
    simpl. rewrite -> rev_snoc. rewrite -> IHl'.
    reflexivity. Qed.

Lemma app_snoc :
  forall (l1 l2 : natlist) (n : nat), snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
Proof.
  intros l1 l2 n. induction l1 as [| m l1'].
  Case "l1 = nil". reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem distr_rev :
  forall l1 l2 : natlist, rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil". simpl. rewrite -> app_nil_end. reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. rewrite -> app_snoc.
    reflexivity. Qed.

(*
次の問題には簡単な解法があります。こんがらがってしまったようであれば、少し戻って
単純な方法を探してみましょう。
 *)

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite <- app_ass. rewrite <- app_ass.
  reflexivity. Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n. induction l as [| m l'].
  Case "l = nil". reflexivity.
  Case "l = cons m l'".
    simpl. rewrite -> IHl'. reflexivity. Qed.

(* 前に書いた nonzeros 関数に関する練習問題です。 *)

Lemma nonzeros_length : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil". reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. destruct n.
    reflexivity. reflexivity. Qed.
(* ☐ *)

(*
リストについての練習問題 (2)

練習問題: ★★, recommended (list_design)

自分で問題を考えましょう。

 ・ cons （::）、 snoc、 append （++）に関する、自明でない定理を考えて書きなさい
    。
 ・ それを証明しなさい。
 *)

Lemma snoc_cons_app :
  forall (l1 l2 : natlist) (n:nat), (snoc l1 n) ++ l2 = l1 ++ n :: l2.
Proof.
  intros l1 l2 n. rewrite -> snoc_append. rewrite -> app_ass.
  simpl. reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★, optional (bag_proofs)

前のバッグについての optional な練習問題に挑戦したのであれば、その定義について、
以下の定理を証明しなさい。
 *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intros s. reflexivity. Qed.

(* 以下の ble_nat に関する補題は、この次の証明に使えるかもしれません。 *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".
    simpl. reflexivity.
  Case "S n'".
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s as [| n s'].
  Case "s = nil". reflexivity.
  Case "s = cons n s'".
    simpl. destruct (beq_nat n 0) as [] _eqn: H.
    SCase "beq_nat n 0 = true".
      rewrite -> ble_n_Sn. reflexivity.
    SCase "beq_nat n 0 = false".
      simpl. rewrite -> H. rewrite -> IHs'. reflexivity.
Qed.

(* ☐ *)

(*
練習問題: ★★★★, optional (rev_injective)

rev 関数が単射である、すなわち
    forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2

であることを証明しなさい。

この練習問題には簡単な解法と難しい解法があります。
 *)

Module PlayGroundRevInjective.

Require Import List.

Lemma rev_snoc :
  forall X (l : list X) (x : X), rev (l ++ x :: nil) = x :: rev l.
Proof.
  intros X l x. induction l as [| x' l'].
  Case "l = nil". reflexivity.
  Case "l = x' :: l'".
    simpl. rewrite -> IHl'. reflexivity. Qed.

Lemma rev_involutive' :
  forall X (l : list X), rev (rev l) = l.
Proof.
  intros X l. induction l as [| x l'].
  Case "l = nil". reflexivity.
  Case "l = cons x l'".
    simpl. rewrite -> rev_snoc. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_injective :
  forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H.
  rewrite <- rev_involutive'.
  rewrite <- H.
  rewrite -> rev_involutive'.
  reflexivity.
Qed.

(* ☐ *)
End PlayGroundRevInjective.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.


Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
    | nil => 42
    | a :: l' => match beq_nat n O with
                   | true => a
                   | false => index_bad (pred n) l'
                 end
  end.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
    | nil => None
    | a :: l' => match beq_nat n O with
                   | true => Some a
                   | false => index (pred n) l'
                 end
  end.


Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4,5,6,7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4,5,6,7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
    | nil => None
    | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Definition option_elim (o : natoption) (d : nat) : nat :=
  match o with
    | Some n' => n'
    | None => d
  end.

(*
練習問題: ★★ (hd_opt)

同じ考え方を使って、以前定義した hd 関数を修正し、 nil の場合に返す値を渡
さなくて済むようにしなさい。
 *)

Definition hd_opt (l : natlist) : natoption :=
  match l with
    | x :: xs => Some x
    | [ ]     => None
  end.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5,6] = Some 5.
Proof. reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★, optional (option_elim_hd)

新しい hd_opt と古い hd の関係についての練習問題です。
 *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim (hd_opt l) default.
Proof.
  intros l default. destruct l as [| x xs].
  Case "l = nil". reflexivity.
  Case "l = case x xs". reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★, recommended (beq_natlist)

数のリストふたつを比較し等価性を判定する関数 beq_natlist の定義を完成させ
なさい。そして、 beq_natlist l l が任意のリスト l で true となることを証
明しなさい。
 *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | x1 :: l1', x2 :: l2' =>
        match beq_nat x1 x2 with
          | true  => beq_natlist l1' l2'
          | false => false
        end
    | [ ], [ ]             => true
    | _ :: _ , [ ]         => false
    | [ ] , _ :: _         => false
  end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1,2,3] [1,2,3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1,2,3] [1,2,4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl :
  forall l:natlist, true = beq_natlist l l.
Proof.
  intros l. induction l as [|n l'].
  Case "l = nil". reflexivity.
  Case "l = cons n l'".
    simpl. rewrite <- beq_nat_refl. rewrite <- IHl'.
    reflexivity. Qed.
(* ☐ *)

Theorem silly1 :
  forall (n m o p : nat),
    n = m ->
    [n,o] = [n,p] ->
    [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.

Theorem silly2 :
  forall (n m o p : nat),
    n = m ->
    (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
    [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

(*
Theorem silly2' :
  forall (n m o p : nat),
    n = m ->
    (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
    [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
Admitted.
 *)

Theorem silly2a :
  forall (n m : nat),
    (n, n) = (m, m) ->
    (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(*
練習問題: ★★, optional (silly_ex)

次の証明を simpl を使わずに完成させなさい。
 *)

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros H0 H1. apply H0. apply H1. Qed.
(* ☐ *)


Theorem silly3_firsttry :
  forall (n : nat),
    true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
Admitted.

Theorem silly3 :
  forall (n : nat),
    true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. apply H. Qed.


(* 練習問題: ★★★, recommended (apply_exercise1) *)

Theorem rev_exercise1 :
  forall (l l' : natlist),
    l = rev l' ->
    l' = rev l.
Proof.
  intros l l' H. rewrite -> H. symmetry. apply rev_involutive. Qed.
(* ☐ *)

(*
練習問題: ★ (apply_rewrite)

apply と rewrite の違いを簡単に説明しなさい。どちらもうまく使えるような場
面はありますか？
 *)

(*
結果の型が一致しているときに使えるのが apply。
equalityが示せているときに使えるのが rewrite。
結果の型がequalityであるときにはどちらも使える場合がある。
 *)
(* ☐ *)

(*
練習問題: ★★, optional (app_ass')

++ の結合則をより一般的な仮定のもとで証明しなさい。（最初の行を変更せずに
）次の証明を完成させること。
 *)

Theorem app_ass' :
  forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1. induction l1 as [ | n l1'].
  Case "l = nil". reflexivity.
  Case "l = cons n l1'".
    simpl. intros l2 l3.
    rewrite -> IHl1'. reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★★ (apply_exercise2)

induction の前に m を intros していないことに注意してください。これによっ
て仮定が一般化され、帰納法の仮定が特定の m に縛られることがなくなり、より
使いやすくなりました。
 *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". reflexivity.
  Case "n = S n'".
    intros m.
    destruct m as [| m'].
      SCase "m = 0". reflexivity.
      SCase "m = S m'".
        simpl. apply IHn'.
Qed.
(* ☐ *)

(*
練習問題: ★★★, recommended (beq_nat_sym_informal)

以下の補題について上の証明と対応する非形式的な証明を書きなさい。

定理: 任意の nat n m について、 beq_nat n m = beq_nat m n。
 *)

(*
証明: n についての帰納法を適用する。
   □ まず n = 0 と置くと以下のようになる
        forall m, beq_nat 0 m = beq_nat m 0
        m = 0 のとき
          beq_nat 0 0 = beq_nat 0 0 で成り立つ
        m = S m' のとき
          beq_nat の定義から、
          beq_nat 0 (S m') = false = beq_nat (S m') 0
          で成り立つ
   □ 次に n = S n' と置き、帰納法の仮定を
        forall m, beq_nat n' m = beq_nat m n'
        とすると、

        m = 0 のとき
          beq_nat (S n') 0 = false = beq_nat 0 (S n')
          で成り立つ
        m = S m' のとき、forall m に注意すると帰納法の仮定から
          beq_nat n' m' = beq_nat m' n'
        も成り立つ。
        これを beq_nat の定義から逆変換すると
          beq_nat (S n') (S m') = beq_nat (S m') (S n')

        これは n = S n ' についても帰納法の仮定が成り立つことを示している ☐
 *)

End NatList.

(* 練習問題: 辞書 *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

(*
この宣言は次のように読めます。「dictionary を構成する方法はふたつある。構
成子 empty で空の辞書を表現するか、構成子 record をキーと値と既存の
dictionary に適用してキーと値の対応を追加した dictionary を構成するかのい
ずれかである」。
 *)

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

(*
下の find 関数は、 dictionary から与えられたキーに対応する値を探し出すも
のです。キーが見つからなかった場合には None に評価され、キーが val に結び
付けられていた場合には Some val に評価されます。同じキーが複数の値に結び
付けられている場合には、最初に見つかったほうの値を返します。
 *)

Fixpoint find (key : nat) (d : dictionary) : option nat :=
  match d with
    | empty => None
    | record k v d' => if (beq_nat key k) then (Some v) else (find key d')
  end.

(* 練習問題: ★ (dictionary_invariant1) *)

Theorem dictionary_invariant1 : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros d k v. simpl. rewrite <- beq_nat_refl. reflexivity. Qed.
(* ☐ *)

(* 練習問題: ★ (dictionary_invariant2) *)

Theorem dictionary_invariant2 : forall (d : dictionary) (m n o: nat),
  (beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
Proof.
  intros d m n o H. simpl. rewrite -> H. reflexivity. Qed.
(* ☐ *)

End Dictionary.

Definition beq_nat_sym := NatList.beq_nat_sym.
