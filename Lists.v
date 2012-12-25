
Require Export Basics.

Module NatLists.

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

(* Check rev. *)

Theorem rev_injective :
  forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2.
Proof. Admitted.
  (*
  intros X l1 l2.
  induction l1 as [| x l1'] _eqn: IH1. induction l2 as [| y l2'] _eqn: IH2.
  Case "l1 = nil, l2 = nil". reflexivity.
  Case "l1 = nil, l2 = cons y l2'".
*)

(* ☐ *)
End PlayGroundRevInjective.



End NatLists.
