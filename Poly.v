
Require Export Lists.


(* 多相的なリスト *)

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length X t)
  end.

Example test_length1 :
length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : (list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
rev nat (cons nat 1 (cons nat 2 (nil nat)))
= (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2 :
rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.

Check app'.
Check app.


(* 引数の同化 *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length' _ t)
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).


(* 暗黙の引数 *)

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length'' t)
  end.

Definition mynil : list nat := nil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Definition list123''' := [1, 2, 3].


(*
練習問題:多相的なリスト

練習問題: ★★, optional (poly_exercises)

ここにあるいくつかの練習問題は、List_J.vにあったものと同じですが、多相性の練
習になります。以下の定義を行い、証明を完成させなさい。
 *)

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
  match count with
    | O => []
    | S count' =>  n :: repeat X n count'
  end.

Example test_repeat1:
repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app :
  forall X:Type, forall l:list X, app [] l = l.
Proof.
  reflexivity. Qed.

Theorem rev_snoc : forall X : Type,
                   forall v : X,
                   forall s : list X,
                     rev (snoc s v) = v :: (rev s).
Proof.
  induction s as [| x s'].
  Case "s = []". reflexivity.
  Case "s = cons x s'".
    simpl. rewrite -> IHs'. reflexivity. Qed.

Theorem snoc_with_append : forall X : Type,
                           forall l1 l2 : list X,
                           forall v : X,
                             snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  induction l1 as [| x l1'].
  Case "s = []". reflexivity.
  Case "s = x :: l1'".
    simpl. intros l2 v. rewrite -> IHl1'. reflexivity. Qed.
(* ☐ *)


(* 多相的なペア *)
Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match (lx,ly) with
    | ([],_) => []
    | (_,[]) => []
    | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Fixpoint combine' {X Y :Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx,ly with
    | [],_ => []
    | _,[] => []
    | x::tx, y ::ty => (x,y) :: (combine' tx ty)
  end.


(*
練習問題: ★ (combine_checks)

次の質問の答えを紙に書いた後で、Coqの出した答えと同じかチェックしなさい。

 ・ 関数combineの型は何でしょう (Check @combineの出力結果は？
 ・ それでは
            Eval simpl in (combine [1,2] [false,false,true,true]).

    は何を出力する？
 *)

(* forall X Y : Type, list X -> list Y -> list (X*Y) *)
Check @combine.

 (* [(1,false), (2,false)] *)
Eval simpl in (combine [1,2] [false,false,true,true]).
(* ☐ *)

(*
練習問題: ★★, recommended (split)

split関数はcombineと全く逆で、ペアのリストを引数に受け取り、リストのペアを返します。多くの関数型言語とで
unzipと呼ばれているものです。次の段落のコメントをはずし、split関数の定義を完成させなさい。続くテストを通過
することも確認しなさい。
 *)

Fixpoint split {X Y : Type} (ps : list (X*Y)) : list X * list Y :=
  match ps with
    | [] => ([], [])
    | (x,y) :: ps' =>
        match split ps' with
          | (xs, ys) => (x :: xs, y :: ys)
        end
  end.

Example test_split :
split [(1,false), (2,false)] = ([1,2], [false,false]).
Proof. reflexivity. Qed.
(* ☐ *)


(* 多相的なオプション *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.


(*
練習問題: ★, optional (hd_opt_poly)

前の章に出てきたhd_opt関数の多相版を定義しなさい。。次の単体テストでの確認も忘れずに。
 *)

Definition hd_opt {X : Type} (l : list X) : option X := index 0 l.

(* 再び、暗黙的に定義された引数を明示的に指定してみましょう。関数名の前に@をつければいいのでしたね。 *)

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1,2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1],[2]] = Some [1].
Proof. reflexivity. Qed.
(* ☐ *)


(* データとしての関数 *)

(* 高階関数 *)

Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.


(* 部分適用 *)

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.


(* 余談：カリー化 *)

(*
練習問題: ★★, optional (currying)

Coqでは、f : A -> B -> Cという型の関数はA -> (B -> C)型と同じです。このことは、もし上の関数fに値Aを与えると、
f' : B -> Cという型の関数が戻り値として返ってくるということです。これは部分適用のplus3でやりましたが、この
ように、複数の引数から戻り値の型のリストを、関数を返す関数として捉えなおすことを、論理学者ハスケル・カリー
にちなんでカリー化、と呼んでいます。

逆に、A -> B -> C型の関数を(A * B) -> C型の関数に変換することもできます。これをアンカリー化（非カリー化）とい
います。アンカリー化された二項演算は、二つの引数を同時にペアの形で与える必要があり、部分適用はできません。

カリー化は以下のように定義できます。
 *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(* 練習問題として、その逆のprod_uncurryを定義し、二つの関数が互いに逆関数であることを証明しなさい。 *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

(* (考える練習: 次のコマンドを実行する前に、prod_curryとprod_uncurryの型を考えなさい。) *)
(* prod_curry : forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z *)
(* prod_uncurry : forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  destruct p as [x y]. reflexivity. Qed.
(* ☐ *)


(* フィルター (Filter)関数 *)

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : (list X) :=
  match l with
    | [] => []
    | h :: t => if test h
                then h :: (filter test t)
                else filter test t
  end.

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
filter length_is_1
       [ [1, 2], [3], [4], [5,6,7], [], [8] ]
= [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.


(* 無名（匿名）関数 *)

Example test_anon_fun':
doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
filter (fun l => beq_nat (length l) 1)
       [ [1, 2], [3], [4], [5,6,7], [], [8] ]
= [ [3], [4], [8] ].
Proof. reflexivity. Qed.


(*
練習問題: ★★, optional (filter_even_gt7)

filter関数を使い、数値のリストを入力すると、そのうち偶数でなおかつ7より大きい要素だけを取り出す
filter_even_gt7関数を書きなさい。
 *)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (ble_nat 8 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.

(* ☐ *)

(*
練習問題: ★★★, optional (partition)

filter関数を使って、partition関数を書きなさい。:
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X

型Xについて、X型の値がある条件を満たすかを調べる述語X -> boolとXのリストlist Xを引数に与えると、partition関
数はリストのペアを返します。ペアの最初の要素は、与えられたリストのうち、条件を満たす要素だけのリストで、二
番目の要素は、条件を満たさないもののリストです。二つのリストの要素の順番は、元のリストの順と同じでなければ
なりません。
 *)

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.
(* ☐ *)


(* マップ（Map）関数 *)
Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.


(*
練習問題: ★★★, optional (map_rev)

mapとrevが可換であることを示しなさい。証明には補題をたてて証明する必要があるでしょう。
 *)

Lemma snoc_map:
  forall (X Y : Type) (f:X -> Y) (l:list X) (x:X),
    map f (snoc l x) = snoc (map f l) (f x).
Proof.
  induction l as [|x' l'].
  Case "l = []". reflexivity.
  Case "l = x' :: l'".
    simpl. intros x. rewrite <- IHl'.
    reflexivity. Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  induction l as [|x l'].
  Case "l = []". reflexivity.
  Case "l = x :: l'".
    simpl. rewrite -> snoc_map. rewrite -> IHl'.
    reflexivity. Qed.
(* ☐ *)

(*
練習問題: ★★, recommended (flat_map)

map関数は、list Xからlist Yへのマップを、型X -> Yの関数を使って実現しています。同じような関数flat_mapを定義
しましょう。これはlist Xからlist Yへのマップですが、X -> list Yとなる関数fを使用できます。このため、次のよ
うに要素ごとの関数fの結果を平坦化してやる必要があります。
        flat_map (fun n => [n,n+1,n+2]) [1,5,10]
      = [1, 2, 3, 5, 6, 7, 10, 11, 12].
 *)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  match l with
    | [] => []
    | x :: l' => f x ++ flat_map f l'
  end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.
(* ☐ *)


Definition option_map {X Y : Type} (f:X -> Y) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.


(*
練習問題: ★★, optional (implicit_args)

filterやmap関数を定義したり使ったりするケースでは、多くの場合暗黙的な型引数が使われます。暗黙の型引数定義
に使われている中括弧を普通の括弧に置き換え、必要なところに型引数を明示的に書くようにして、それが正しいかど
うかをCoqでチェックしなさい。
 *)

Fixpoint filter' (X:Type) (test: X -> bool) (l:list X) : (list X) :=
  match l with
    | [] => []
    | h :: t => if test h
                then h :: (filter' X test t)
                else filter' X test t
  end.

Example test_filter'1: filter' nat evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Example test_filter'2:
filter' (list nat) (fun l => beq_nat (length l) 1)
       [ [1, 2], [3], [4], [5,6,7], [], [8] ]
= [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Fixpoint map' (X Y:Type) (f:X -> Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.

Example test_map'1: map' nat nat (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.

Example test_map'2: map' nat bool oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.
(* ☐ *)


(* 畳み込み（Fold）関数 *)

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
    | nil => b
    | h :: t => f h (fold f t b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.


(*
練習問題: ★, optional (fold_types_different)

fold関数がXとY二つの型引数をとっていて、関数fが型Xを引数にとり型Yを返すようになっていることに注目し
てください。XとYが別々の型となっていることで、どのような場合に便利であるかを考えてください。
 *)

(*
たとえば要素Xから要素のリスト(Y=[X])を作っていくような関数のときに便利である。
以下、fold を使って定義した filter の例。
 *)

Definition filter'' {X:Type} (test: X -> bool) (l:list X) : (list X) :=
  fold (fun x l' => if test x then x :: l' else l') l [].

Example test_filter''1: filter'' evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Example test_filter''2:
filter'' (fun l => beq_nat (length l) 1)
         [ [1, 2], [3], [4], [5,6,7], [], [8] ]
= [ [3], [4], [8] ].
Proof. reflexivity. Qed.


(* 関数を作成する関数 *)

Definition constfun {X : Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X: Type} (f: nat -> X) (k:nat) (x:X) : nat -> X :=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.


(*
練習問題: ★ (override_example)

次の証明にとりかかる前に、あなたがこの証明の意味することを理解し
ているか確認するため、証明内容を別の言葉で言い換えてください。証
明自体は単純なものです。
 *)

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof. reflexivity. Qed.
(* ☐ *)

(*
forall b : bool, override (constfun b) 3 true
は 3 を渡したときにtrue を返し、
それ以外を渡したときに b を返す関数である。
この関数に 2 を渡したときには b が返ることを証明する。
 *)


(* さらにCoqについて *)

(* unfoldタクティック *)

Theorem unfold_example_bad :
  forall m n, 3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  Admitted.

Theorem unfold_example :
  forall m n, 3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity. Qed.

Theorem override_eq :
  forall {X:Type} x k (f:nat -> X), (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity. Qed.


(* 練習問題: ★★ (override_neq) *)

Theorem override_neq :
  forall {X:Type} x1 x2 k1 k2 (f : nat -> X),
    f k1 = x1 ->
    beq_nat k2 k1 = false ->
    (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H0 H1.
  unfold override. rewrite -> H1.
  apply H0.
Qed.
(* ☐ *)

Theorem eq_add_S :
  forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly4 :
  forall (n m : nat), [n] = [m] -> n = m.
Proof.
  intros n o eq. inversion eq. reflexivity. Qed.

Theorem silly5 :
  forall (n m o : nat), [n,m] = [o,o] -> [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.


(* 練習問題: ★ (sillyex1) *)

Example sillyex1 :
forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j eq0 eq1.
  inversion eq0.
  inversion eq1.
  rewrite <- H0.
  reflexivity.
Qed.
(* ☐ *)

Theorem silly6 :
  forall (n : nat), S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 :
  forall (n m : nat), false = true -> [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.


(* 練習問題: ★ (sillyex2) *)

Example sillyex2 :
forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros X x y z l j contra eq.
  inversion contra.
Qed.
(* ☐ *)

Lemma eq_remove_S :
  forall n m, n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

Theorem beq_nat_eq :
  forall n m, true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. intros contra. inversion contra.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
    apply eq_remove_S. apply IHn'. apply H. Qed.


(*
練習問題: ★★ (beq_nat_eq_informal)

beq_nat_eqの、非形式的な証明を示しなさい。
 *)

(*
forall n m, true = beq_nat n m -> n = m.
任意の自然数 n m について、
beq_nat n m = true ならば n = m であることを示す

自然数 n についての帰納法を適用する
- n = 0 のとき
  m = 0 ならば beq_nat 0 0 は true で 0 = 0 なので成立
  m = S m' ならば beq_nat 0 m は false で前提が成立しないので成立
- n = S n' のとき
  m = 0 ならば beq_nat (S n') 0 は false で前提が成立しないので成立
  m = S m' ならば
     beq_nat (S n') (S m') = beq_nat n' m'
     また、帰納法の仮定から、
     全ての m について beq_nat n' m ならば n' = m
     つまり m' についても beq_nat n' m' ならば n' = m'
     n' = m' のときには S n' = S m'
     つまり
     beq_nat (S n') (S m') ならば S n' = S m' が成立。
     これは n = S n' のときにも帰納法の仮定が成立することを示している。
 *)

(* ☐ *)

(*
練習問題: ★★★ (beq_nat_eq')

beq_nat_eqは、mについて帰納法をつかうことで証明すること
ができました。しかし我々は、もう少し変数を導入する順序に
注意を払うべきです。なぜなら、我々は一般に、十分な帰納法
の仮定を得ているからです。このことを次に示します。次の証
明を完成させなさい。この練習問題の効果を最大にするため、
とりあえずは先にやった証明を見ないで取り組んでください。
 *)

Theorem beq_nat_eq' :
  forall m n, beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m'].
  (* m = 0 *)
    destruct n as [| n'].
    (* n = 0 *) intros H0. reflexivity.
    (* n = S n' *) simpl. intros contra. inversion contra.
  (* m = S m' *)
    destruct n as [| n'].
    (* n = 0 *) simpl. intros contra. inversion contra.
    (* n = S n' *)
      simpl. intro H0.
      apply eq_remove_S.
      apply (IHm' n' H0).
Qed.
(* ☐ *)


Theorem length_snoc' :
  forall (X : Type) (v : X) (l : list X) (n : nat),
    length l = n ->
    length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity.
Qed.

(*
練習問題: ★★, optional (practice)

同じところに分類され、相互に関連するような、自明でもないが複雑と
いうほどでもない証明をいくつか練習問題としましょう。このうち、い
くつかは過去のレクチャーや練習問題に出てきた補題を使用します。
 *)

Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  intros n H.
  destruct n as [| n'].
    reflexivity.
    inversion H.
Qed.

Theorem beq_nat_0_l' : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  apply beq_nat_eq.
Qed.

Theorem beq_nat_0_r : forall n,
  true = beq_nat n 0 -> 0 = n.
Proof.
  intros n H.
  destruct n as [| n'].
    reflexivity.
    inversion H.
Qed.

Theorem beq_nat_0_r' : forall n,
  true = beq_nat n 0 -> 0 = n.
Proof.
  symmetry.
  apply (beq_nat_eq n 0 H).
Qed.
(* ☐ *)


Theorem double_injecitve :
  forall n m, double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". simpl. intros m eq. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros m eq. destruct m as [| m'].
    SCase "m = 0". inversion eq.
    SCase "m = S m'".
      apply eq_remove_S. apply IHn'. inversion eq. reflexivity.
Qed.


(* タクティックを仮定に使用する *)

Theorem S_inj :
  forall (n m : nat) (b : bool), beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' :
  forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.


(*
練習問題: ★★★, recommended (plus_n_n_injective)

先に述べた"in"を使って次の証明をしなさい。
 *)

Theorem plus_n_n_injective :
  forall n m, n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    destruct m as [| m'].
      reflexivity.

      intros H. inversion H.
  Case "n = S n'".
    intros m H.
    destruct m as [| m'].
      inversion H.

      rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H.
      simpl in H. inversion H.

      apply eq_remove_S. apply IHn'.
      apply H1.
Qed.
(* ☐ *)


Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false :
  forall (n : nat), sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 5 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity. Qed.


(* 練習問題: ★ (override_shadow) *)

Theorem override_shadow :
  forall {X:Type} x1 x2 k1 k2 (f : nat -> X),
    (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  unfold override.
  intros X x1 x2 k1 k2.
  destruct (beq_nat k1 k2).
  reflexivity. reflexivity.
 Qed.
(* ☐ *)

(* 練習問題: ★★★, recommended (combine_split) *)

Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [ | [x y] l'].
  Case "l = []".
    intros l1 l2 H.
    inversion H.
    reflexivity.
  Case "l = [x y] :: l'".
    intros l1 l2 H.
    simpl in H.
    destruct (split l') as [ xs ys ].
    inversion H.
    simpl.
    rewrite -> (IHl' xs ys (eq_refl (xs, ys))).
    reflexivity.
Qed.
(* ☐ *)

(*
練習問題: ★★★, optional (split_combine)

思考練習: 我々はすでに、全ての型のリストのペアでcombineがsplitの
逆関数であることを証明しました。ではその逆の「splitはcombineの逆
関数である」を示すことはできるでしょうか？

ヒント: split combine l1 l2 = (l1,l2)がtrueとなるl1、l2の条件は
何でしょう？

この定理をCoqで証明しなさい（なるべくintrosを使うタイミングを遅
らせ、帰納法の仮定を一般化させておくといいでしょう。
 *)

Theorem split_combine :
  forall X Y (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  induction l1 as [| x l1'].
  (* l1 = [] *)
    destruct l2 as [| y l2'].
    (* l2 = [] *) reflexivity.
    (* l2 = y :: l2' *)
      simpl. intro H. inversion H.
  (* l1 = x :: l1' *)
    intros l2 H.
    destruct l2 as [| y l2'].
      (* l2 = [] *) inversion H.
      (* l2 = y :: l2' *)
         simpl.
         rewrite -> (IHl1' l2').
         reflexivity.
         simpl in H. inversion H.
         reflexivity.
Qed.
(* ☐ *)


(* rememberタクティック *)
Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem sillyfun1_odd_FAILED :
  forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
Admitted.

Theorem sillyfun1_odd :
  forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  destruct e3.
    Case "e3 = true". apply beq_nat_eq in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
      remember (beq_nat n 5) as e5. destruct e5.
        SCase "e5 = true".
          apply beq_nat_eq in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false".
          inversion eq. Qed.

(* destruct ... as ... _eqn: ... による別解 *)
Theorem sillyfun1_odd' :
  forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) as [|] _eqn: Heqe3.
    Case "beq_nat n 3 = true".
      (* rewrite -> (beq_nat_eq n 3 (eq_sym Heqe3)). *)
      symmetry in Heqe3. apply beq_nat_eq in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "beq_nat n 3 = false".
      destruct (beq_nat n 5) as [|] _eqn: Heqe5.
        SCase "beq_nat n 5 = true".
          symmetry in Heqe5. apply beq_nat_eq in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "beq_nat n 5 = false".
          inversion eq. Qed.


(* 練習問題: ★★ (override_same) *)

Theorem override_same :
  forall {X:Type} x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f eq.
  unfold override.
  remember (beq_nat k1 k2) as d12.
  destruct d12.
  (* d12 = true *)
    apply beq_nat_eq in Heqd12.
    rewrite <- Heqd12. rewrite -> eq.
    reflexivity.
  (* d12 = false *) reflexivity.
Qed.
(* ☐ *)

(*
練習問題: ★★★, optional (filter_exercise)

この問題はやや難しいかもしれません。最初にintrosを使うと、帰納法
を適用するための変数まで上に上げてしまうので気をつけてください。
 *)

Theorem filter_exercise :
  forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf ->
    test x = true.
Proof.
  induction l as [| x' l'].
  (* l = [] *) simpl. intros lf eq. inversion eq.
  (* l = x' :: l' *)
    simpl. remember (test x') as tx'.
    destruct tx'.
    (* tx' = true *)
      intros lf eq. inversion eq.
      rewrite <- H0. rewrite <- Heqtx'.
      reflexivity.
    (* tx' = false *) apply IHl'.
Qed.
(* ☐ *)


(* apply ... with ...タクティック *)

Example trans_eq_example :
forall (a b c d e f : nat),
  [a,b] = [c,d] ->
  [c,d] = [e,f] ->
  [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq :
  forall {X:Type} (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' :
forall (a b c d e f : nat),
  [a,b] = [c,d] ->
  [c,d] = [e,f] ->
  [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2. Qed.

Example trans_eq_example'' :
forall (a b c d e f : nat),
  [a,b] = [c,d] ->
  [c,d] = [e,f] ->
  [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with [c,d]. apply eq1. apply eq2. Qed.

Example trans_eq_example''' :
forall (a b c d e f : nat),
  [a,b] = [c,d] ->
  [c,d] = [e,f] ->
  [a,b] = [e,f].
Proof.
  intros a b c d e f.
  apply (trans_eq [a,b] [c,d]). Qed.


(* 練習問題: ★★★, recommended (apply_exercises) *)

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply (trans_eq (n + p) m). apply eq2. apply eq1. Qed.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_eq in eq1. apply beq_nat_eq in eq2.
  rewrite -> (trans_eq n m p eq1 eq2).
  apply beq_nat_refl.
Qed.

Theorem override_permute :
  forall {X:Type} x1 x2 k1 k2 k3 (f : nat -> X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 =
  (override (override f k1 x1) k2 x2) k3.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k3) as [|] _eqn: Hd13.
  (* Hd13 = true *)
    symmetry in Hd13. apply beq_nat_eq in Hd13.
    destruct (beq_nat k2 k3) as [|] _eqn: Hd23.
    (* Hd23 = true *)
      symmetry in Hd23. apply beq_nat_eq in Hd23.
      rewrite -> Hd13 in H. rewrite -> Hd23 in H.
      rewrite <- beq_nat_refl in H.
      inversion H.
    (* Hd23 = false *) reflexivity.
  (* Hd13 = false *) reflexivity.
Qed.
(* ☐ *)


(* まとめ *)

(* さらなる練習問題 *)

(*
練習問題: ★★, optional (fold_length)

リストに関する多くの一般的な関数はfoldを使って書きなおすることが
できます。例えば、次に示すのはlengthの別な実装です。
 *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

(* fold_lengthが正しいことを証明しなさい。 *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Admitted.
(* ☐ *)

(*
練習問題: ★★★, recommended (fold_map)

map関数もfoldを使って書くことができます。以下のfold_mapを完成さ
せなさい。
 *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x ys => cons (f x) ys) l [].


(* fold_mapの正しさを示す定理をCoqで書き、証明しなさい *)
Theorem map_fold_map_eq :
  forall {X Y:Type} (f : X -> Y) (l : list X),
    map f l = fold_map f l.
Proof.
  intros.
  induction l as [| x l'].
  (* l = [] *) reflexivity.
  (* l = x :: l' *)
    unfold fold_map. unfold fold.
    fold (fold (fun x ys => cons (f x) ys) l').
    fold (fold_map f l').
    simpl.
    rewrite <- IHl'.
    reflexivity.
Qed.
(* ☐ *)

Module MumbleBaz.

(*
練習問題: ★★, optional (mumble_grumble)

つぎの、機能的に定義された二つの型をよく観察してください。
 *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(*
次の式のうち、ある型Xについてgrumble Xの要素として正しく定義され
ているものはどれでしょうか。

 ・ d (b a 5)
      正しい
 ・ d mumble (b a 5)
      正しくない -- mumble は mumble型の値ではない
 ・ d bool (b a 5)
      正しくない -- bool は mumble型の値ではない
 ・ e bool true
      正しくない -- e bool は grumble bool 型の値だが引数を取らない
 ・ e mumble (b c 0)
      正しくない -- e mumble は grumble mumble 型の値だが引数を取らない
 ・ e bool (b c 0)
      正しくない -- e bool は grumble bool 型の値だが引数を取らない
 ・ c
      正しい
 *)

(* ☐ *)

(*
練習問題: ★★, optional (baz_num_elts)

次の、機能的に定義された型をよく観察してください。
 *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(* 型bazはいくつの要素を持つことができるでしょうか？ *)

(*
要素数は0。
baz から baz を作ることはできるが、
単位元となる baz を作る方法が無い。
 *)
(* ☐ *)

End MumbleBaz.


(*
練習問題: ★★★★, recommended (forall_exists_challenge)

チャレンジ問題: 二つの再帰関数forallb、existsbを定義しなさい。
forallbは、リストの全ての要素が与えられた条件を満たしているかど
うかを返します。
      forallb oddb [1,3,5,7,9] = true

      forallb negb [false,false] = true

      forallb evenb [0,2,4,5] = false

      forallb (beq_nat 5) [] = true
 *)

Fixpoint forallb {X:Type} (f:X -> bool) (l:list X) :=
  match l with
    | [] => true
    | x :: l' => match f x with
                   | false => false
                   | true => forallb f l'
                 end
  end.

Goal forallb oddb [1,3,5,7,9] = true.
Proof. reflexivity. Qed.

Goal forallb negb [false,false] = true.
Proof. reflexivity. Qed.

Goal forallb evenb [0,2,4,5] = false.
Proof. reflexivity. Qed.

Goal forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.

(*
existsbは、リストの中に、与えられた条件を満たす要素が一つ以上あ
るかを返します。
      existsb (beq_nat 5) [0,2,3,6] = false

      existsb (andb true) [true,true,false] = true

      existsb oddb [1,0,0,0,0,3] = true

      existsb evenb [] = false
 *)

Fixpoint existsb {X:Type} (f:X -> bool) (l:list X) :=
  match l with
    | [] => false
    | x :: l' => match f x with
                   | true => true
                   | false => existsb f l'
                 end
  end.

Goal existsb (beq_nat 5) [0,2,3,6] = false.
Proof. reflexivity. Qed.

Goal existsb (andb true) [true,true,false] = true.
Proof. reflexivity. Qed.

Goal existsb oddb [1,0,0,0,0,3] = true.
Proof. reflexivity. Qed.

Goal existsb evenb [] = false.
Proof. reflexivity. Qed.


(*
次にexistsb'を再帰関数としてではなく、forallbとnegbを使って定義
しなさい。.

そして、existsb'とexistsbが同じ振る舞いをすることを証明しなさい。
 *)

Definition existsb' {X:Type} (f:X -> bool) l :=
  negb (forallb (fun x => negb (f x)) l).

Goal existsb' (beq_nat 5) [0,2,3,6] = false.
Proof. reflexivity. Qed.

Goal existsb' (andb true) [true,true,false] = true.
Proof. reflexivity. Qed.

Goal existsb' oddb [1,0,0,0,0,3] = true.
Proof. reflexivity. Qed.

Goal existsb' evenb [] = false.
Proof. reflexivity. Qed.


Theorem existb_existb'_eq :
  forall {X:Type} (f:X -> bool) (l:list X),
    existsb f l = existsb' f l.
Proof.
  induction l as [| x l'].
  (* l = [] *) reflexivity.
  (* l = x :: l' *)
    unfold existsb'.
    simpl.
    destruct (f x).
    (* f x = true *)
      simpl. reflexivity.
    (* f x = false *)
      simpl. fold (existsb' f l'). apply IHl'.
Qed.

(* ☐ *)

(*
練習問題: ★★, optional (index_informal)

index関数の定義を思い出してください。
   Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else index (pred n) l'
     end.

次の定理の、非形式的な証明を書きなさい。
   forall X n l, length l = n -> @index X (S n) l = None.
 *)

(*
証明:
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

(* Goal forall X n l, length l = n -> @index X (S n) l = None. *)
Goal forall X l n, length l = n -> @index X (S n) l = None.
Proof.
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
      intro eq. inversion eq.
      rewrite -> H0.
      apply (IHl' n' H0).
Qed.
