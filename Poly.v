
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

