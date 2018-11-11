module RBTree

open FStar.Math.Lib

type colour =
  | Red: colour
  | Black: colour

type tree =
  | Leaf: tree
  | Node: c:colour -> l:tree -> v:int -> r:tree -> tree

val get_rcol: tree -> GTot colour
let get_rcol t = match t with
  | Leaf -> Black
  | Node c _ _ _ -> c

// childs of red nodes are black
val red_black_childs: tree -> GTot bool
let rec red_black_childs t = match t with
  | Leaf -> true
  | Node c l v r -> red_black_childs l
		&& red_black_childs r
		&& (c <> Red || (get_rcol l = Black 
			    && get_rcol r = Black))

val gmember: tree -> int -> GTot bool
let rec gmember t x = match t with
  | Leaf -> false
  | Node _ l v r -> v = x || gmember l x || gmember r x

val max_elem: t:tree{Node? t} -> GTot int
let rec max_elem t = match t with
  | Node _ _ v Leaf -> v
  | Node _ _ _ r -> max_elem r

val min_elem: t:tree{Node? t} -> GTot int
let rec min_elem t = match t with
  | Node _ Leaf v _ -> v
  | Node _ l _ _ -> min_elem l

val max_gmember: t:tree{Node? t} ->
  Lemma (gmember t (max_elem t))
  [SMTPat (gmember t (max_elem t))]
let rec max_gmember t = match t with
  | Node _ _ v Leaf -> ()
  | Node _ _ _ r -> max_gmember r

val min_gmember: t:tree{Node? t} ->
  Lemma (gmember t (min_elem t))
  [SMTPat (gmember t (min_elem t))]
let rec min_gmember t = match t with
  | Node _ Leaf v _ -> ()
  | Node _ l _ _ -> min_gmember l

val gt_max: v:int -> t:tree -> GTot bool
let gt_max v t = if Node? t then v > max_elem t
			    else true

val lt_min: v:int -> t:tree -> GTot bool
let lt_min v t = if Node? t then v < min_elem t
			    else true
// Definition from https://github.com/FStarLang/FStar/blob/master/examples/data_structures/RBTree.fst
val sorted: tree -> GTot bool
let rec sorted t = match t with
  | Leaf -> true
  | Node _ l v r -> sorted l
		&& sorted r
		&& (if Node? l then v > max_elem l else true)
		&& (if Node? r then v < min_elem r else true)

val sorted_vals : tree -> GTot Type0
let rec sorted_vals = function
  | Leaf -> True
  | Node _ l v r -> (forall x. gmember l x ==> x < v)
		 /\ (forall x. gmember r x ==> v < x)
		 /\ sorted_vals l
		 /\ sorted_vals r

val min_elem_min': t:tree{Node? t /\ sorted t} ->
  Lemma (forall x. gmember t x ==> x >= min_elem t)
val max_elem_max': t:tree{Node? t /\ sorted t} ->
  Lemma (forall x. gmember t x ==> x <= max_elem t)
let rec min_elem_min' t = match t with
  | Node _ Leaf _ Leaf -> ()
  | Node _ Leaf _ r -> min_elem_min' r
  | Node _ l _ Leaf -> min_elem_min' l; max_elem_max' l
  | Node _ l v r -> min_elem_min' l; min_elem_min' r;
    max_elem_max' l
and max_elem_max' t = match t with
  | Node _ Leaf _ Leaf -> ()
  | Node _ l _ Leaf -> max_elem_max' l
  | Node _ Leaf _ r -> max_elem_max' r; min_elem_min' r
  | Node _ l v r -> max_elem_max' r; max_elem_max' l;
    min_elem_min' r

val min_elem_min: t:tree{Node? t /\ sorted t} -> x:int {gmember t x} ->
  Lemma (x >= min_elem t)
let min_elem_min t x = min_elem_min' t

val max_elem_max: t:tree{Node? t /\ sorted t} -> x:int {gmember t x} ->
  Lemma (x <= max_elem t)
let max_elem_max t x = max_elem_max' t

val min_min_elem: t:tree -> v:int ->
  Lemma (requires Node? t /\ (forall x. gmember t x ==> x >= v))
  (ensures v <= min_elem t)
let rec min_min_elem t v = match t with
  | Node _ Leaf x _ -> ()
  | Node _ l _ _ -> min_min_elem l v

val max_max_elem: t:tree -> v:int ->
  Lemma (requires Node? t /\ (forall x. gmember t x ==> x <= v))
  (ensures v >= max_elem t)
let rec max_max_elem t v = match t with
  | Node _ _ x Leaf -> ()
  | Node _ _ _ r -> max_max_elem r v

val min_transform': t1:tree -> t2:tree ->
  Lemma (requires sorted t1 /\ sorted t2 /\ Node? t1
    /\ (forall x. gmember t1 x ==> gmember t2 x))
    (ensures min_elem t1 >= min_elem t2)
let min_transform' t1 t2 = min_elem_min t2 (min_elem t1)

val min_transform: t1:tree -> t2:tree ->
  Lemma (requires sorted t1 /\ sorted t2 /\ Node? t1
    /\ (forall x. gmember t1 x <==> gmember t2 x))
    (ensures min_elem t1 == min_elem t2)
let min_transform t1 t2 = min_elem_min t1 (min_elem t2);
  min_elem_min t2 (min_elem t1)

val max_transform': t1:tree -> t2:tree ->
  Lemma (requires sorted t1 /\ sorted t2 /\ Node? t1
    /\ (forall x. gmember t1 x ==> gmember t2 x))
    (ensures max_elem t1 <= max_elem t2)
let max_transform' t1 t2 = max_elem_max t2 (max_elem t1)

val max_transform: t1:tree -> t2:tree ->
  Lemma (requires sorted t1 /\ sorted t2 /\ Node? t1
    /\ (forall x. gmember t1 x <==> gmember t2 x))
    (ensures max_elem t1 == max_elem t2)
let max_transform t1 t2 = max_elem_max t1 (max_elem t2);
  max_elem_max t2 (max_elem t1)

val sorted_sorted_vals: t:tree ->
  Lemma (requires sorted t)
  (ensures sorted_vals t)
let rec sorted_sorted_vals t = match t with
  | Leaf -> ()
  | Node _ Leaf v Leaf -> ()
  | Node _ l v Leaf -> sorted_sorted_vals l;
    max_elem_max' l
  | Node _ Leaf v r -> sorted_sorted_vals r;
    min_elem_min' r
  | Node _ l v r -> sorted_sorted_vals l;
    sorted_sorted_vals r;
    min_elem_min' r; max_elem_max' l

val sorted_vals_sorted: t:tree ->
  Lemma (requires sorted_vals t)
  (ensures sorted t)
let rec sorted_vals_sorted t = match t with
  | Leaf -> ()
  | Node _ Leaf v Leaf -> ()
  | Node _ l v Leaf -> sorted_vals_sorted l;
    assert (gmember l (max_elem l))
  | Node _ Leaf v r -> sorted_vals_sorted r;
    assert (gmember r (min_elem r))
  | Node _ l v r -> sorted_vals_sorted l;
    sorted_vals_sorted r; assert (gmember l (max_elem l));
    assert (gmember r (min_elem r))

val member: t:tree{sorted t} -> x:int -> Tot bool
let rec member t x = match t with
    | Leaf -> false
    | Node _ l v r -> if x = v then true
		     else if x < v then member l x
		     else member r x

val member_correct: t:tree{sorted t} -> x:int ->
  Lemma (gmember t x <==> member t x)
let rec member_correct t x = match t with
  | Leaf -> ()
  | Node _ l v r -> if x = v then ()
		   else if x < v then (
		     if Node? r then min_elem_min' r else ();
		     assert (~(gmember r x));
		     member_correct l x
		   ) else (
		     if Node? l then max_elem_max' l else ();
		     assert (~(gmember l x));
		     member_correct r x
		   )

val black_height: tree -> GTot nat
let rec black_height t = match t with
  | Leaf -> 0
  | Node Red l _ r -> max (black_height l) (black_height r)
  | Node Black l _ r -> 1 + max (black_height l) (black_height r)


val black_height_correct: tree -> GTot bool
let rec black_height_correct t = match t with
  | Leaf -> true
  | Node _ l _ r -> black_height_correct l
	 && black_height_correct r
	 && black_height l = black_height r

// RBTree with posibly red root/subtree of rbtree
val is_srbtree: t:tree -> GTot bool
let is_srbtree t = sorted t && red_black_childs t && black_height_correct t

val is_rbtree: t:tree -> GTot bool
let is_rbtree t = is_srbtree t && get_rcol t = Black

val ired_red : tree -> GTot bool
let ired_red t = match t with
  | Node Red (Node Red a _ b) _ c
  | Node Red a _ (Node Red b _ c) ->
    let ba = black_height a in
    is_rbtree a && is_rbtree b && is_rbtree c
    && ba = black_height b && ba = black_height c
    && sorted t
  | _ -> false

val icase1 : tree -> GTot bool
let icase1 t = match t with
  | Node Black (Node Red a _ (Node Red b _ c)) _ (Node Red d _ e)
  | Node Black (Node Red (Node Red a _ b) _ c) _ (Node Red d _ e)
  | Node Black (Node Red a _ b) _ (Node Red c _ (Node Red d _ e))
  | Node Black (Node Red a _ b) _ (Node Red (Node Red c _ d) _ e) ->
    let ba = black_height a in
    is_rbtree a && is_rbtree b && is_rbtree c && is_rbtree d
    && is_rbtree e && ba = black_height b && ba = black_height c
    && ba = black_height d && ba = black_height e
    && sorted t
  | _ -> false
	 
val icase2 : tree -> GTot bool
let icase2 t = match t with
  | Node Black (Node Red a _ (Node Red b _ c)) _ d
  | Node Black a _ (Node Red (Node Red b _ c) _ d) ->
    let ba = black_height a in
    is_rbtree a && is_rbtree b && is_rbtree c && is_rbtree d
    && ba = black_height b && ba = black_height c 
    && ba = black_height d && sorted t
  | _ -> false

val icase3 : tree -> GTot bool
let icase3 t = match t with
  | Node Black (Node Red (Node Red a _ b) _ c) _ d
  | Node Black a _ (Node Red b _ (Node Red c _ d)) ->
    let ba = black_height a in
    is_rbtree a && is_rbtree b && is_rbtree c && is_rbtree d
    && ba = black_height b && ba = black_height c
    && ba = black_height d && sorted t
  | _ -> false

val pre_balance : pc:colour -> t:tree -> GTot bool
let pre_balance pc t = match pc with
  | Black -> is_srbtree t || icase1 t || icase2 t || icase3 t
			 || ired_red t
  | Red -> is_srbtree t || icase1 t || icase2 t || icase3 t

val post_balance : pc:colour -> t:tree -> GTot bool
let post_balance pc t = match pc with
  | Black -> is_srbtree t || ired_red t
  | Red -> is_srbtree t

val insert_fixup_c1 : t:tree {icase1 t} -> Tot tree
let insert_fixup_c1 t = match t with
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 (Node Red d v4 e) -> 
      Node Red (Node Black (Node Red a v1 b) v2 c) v3 (Node Black d v4 e)
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 (Node Red d v4 e) -> 
      Node Red (Node Black a v1 (Node Red b v2 c)) v3 (Node Black d v4 e)
   | Node Black (Node Red a v1 b) v2 (Node Red (Node Red c v3 d) v4 e) ->
      Node Red (Node Black a v1 b) v2 (Node Black (Node Red c v3 d) v4 e)
   | Node Black (Node Red a v1 b) v2 (Node Red c v3 (Node Red d v4 e)) ->
      Node Red (Node Black a v1 b) v2 (Node Black c v3 (Node Red d v4 e))

val insert_fixup_c1_sorted : t:tree {icase1 t} -> 
			   Lemma (sorted (insert_fixup_c1 t))
let insert_fixup_c1_sorted t = match t with
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 (Node Red d v4 e) -> ()
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 (Node Red d v4 e) -> ()
   | Node Black (Node Red a v1 b) v2 (Node Red (Node Red c v3 d) v4 e) -> ()
   | Node Black (Node Red a v1 b) v2 (Node Red c v3 (Node Red d v4 e)) -> ()

val insert_fixup_c1_member : t:tree {icase1 t} ->
			   Lemma (forall x. gmember t x <==> 
			   gmember (insert_fixup_c1 t) x)
let insert_fixup_c1_member t = match t with
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 (Node Red d v4 e) -> ()
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 (Node Red d v4 e) -> ()
   | Node Black (Node Red a v1 b) v2 (Node Red (Node Red c v3 d) v4 e) -> ()
   | Node Black (Node Red a v1 b) v2 (Node Red c v3 (Node Red d v4 e)) -> ()

val insert_fixup_c1_height : t:tree {icase1 t} ->
			  Lemma (black_height t ==
			  black_height (insert_fixup_c1 t))
let insert_fixup_c1_height t = match t with
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 (Node Red d v4 e) -> ()
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 (Node Red d v4 e) -> ()
   | Node Black (Node Red a v1 b) v2 (Node Red (Node Red c v3 d) v4 e) -> ()
   | Node Black (Node Red a v1 b) v2 (Node Red c v3 (Node Red d v4 e)) -> ()

val insert_fixup_c1_post_balance : pc:colour -> t:tree {icase1 t} ->
			Lemma (post_balance pc (insert_fixup_c1 t))
let insert_fixup_c1_post_balance pc t = insert_fixup_c1_sorted t;
   insert_fixup_c1_height t;
   let t' = insert_fixup_c1 t in
   match t with
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 (Node Red d v4 e)
     -> assert (is_srbtree t')
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 (Node Red d v4 e)
     -> assert (is_srbtree t')
   | Node Black (Node Red a v1 b) v2 (Node Red (Node Red c v3 d) v4 e)
     -> assert (is_srbtree t')
   | Node Black (Node Red a v1 b) v2 (Node Red c v3 (Node Red d v4 e))
     -> assert (is_srbtree t')
  
val insert_fixup_c23 : t:tree {icase2 t \/ icase3 t} -> Tot tree
let insert_fixup_c23 t = match t with
  // case 2
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 d
   | Node Black a v1 (Node Red (Node Red b v2 c) v3 d)
  // case 3
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 d
   | Node Black a v1 (Node Red b v2 (Node Red c v3 d)) ->
      Node Black (Node Red a v1 b) v2 (Node Red c v3 d)

val insert_fixup_c23_member : t:tree {icase2 t \/ icase3 t} ->
			   Lemma (forall x. gmember t x <==> 
			   gmember (insert_fixup_c23 t) x)
let insert_fixup_c23_member t = match t with
  // case 2
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 d -> ()
   | Node Black a v1 (Node Red (Node Red b v2 c) v3 d) -> ()
  // case 3
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 d -> ()
   | Node Black a v1 (Node Red b v2 (Node Red c v3 d)) -> ()

val insert_fixup_c2_step : t:tree {icase2 t} ->
			  GTot (t':tree {icase3 t'})
let insert_fixup_c2_step = function 
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 d -> 
     Node Black (Node Red (Node Red a v1 b) v2 c) v3 d
   | Node Black a v1 (Node Red (Node Red b v2 c) v3 d) ->
     Node Black a v1 (Node Red b v2 (Node Red c v3 d)) 

val insert_fixup_c2_step_ok: t:tree {icase2 t} ->
     Lemma ((insert_fixup_c23 t) == (insert_fixup_c23 (insert_fixup_c2_step t)))
let insert_fixup_c2_step_ok = function
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 d -> ()
   | Node Black a v1 (Node Red (Node Red b v2 c) v3 d) -> ()

val insert_fixup_c3_sorted : t:tree {icase3 t} -> 
			   Lemma (sorted (insert_fixup_c23 t))
let insert_fixup_c3_sorted t = match t with
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 d -> ()
   | Node Black a v1 (Node Red b v2 (Node Red c v3 d)) -> ()

val insert_fixup_c2_sorted: t:tree {icase2 t} ->
                          Lemma (sorted (insert_fixup_c23 t))
let insert_fixup_c2_sorted t = let t' = insert_fixup_c2_step t in
      insert_fixup_c2_step_ok t;
      insert_fixup_c3_sorted t'

val insert_fixup_c23_sorted: t:tree {icase2 t \/ icase3 t} ->
  Lemma (sorted (insert_fixup_c23 t))
let insert_fixup_c23_sorted t = match t with
  // case 2
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 d
   | Node Black a v1 (Node Red (Node Red b v2 c) v3 d) ->
     insert_fixup_c2_sorted t
  // case 3
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 d
   | Node Black a v1 (Node Red b v2 (Node Red c v3 d)) ->
     insert_fixup_c3_sorted t

val insert_fixup_c23_heigth : t:tree {icase2 t \/ icase3 t} ->
			  Lemma (black_height t ==
			  black_height (insert_fixup_c23 t))
let insert_fixup_c23_heigth t = match t with
  // case 2
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 d -> ()
   | Node Black a v1 (Node Red (Node Red b v2 c) v3 d) -> ()
  // case 3
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 d -> ()
   | Node Black a v1 (Node Red b v2 (Node Red c v3 d)) -> ()

val insert_fixup_c23_post_balance : pc:colour 
                        -> t:tree {icase2 t \/ icase3 t} ->
			Lemma (post_balance pc (insert_fixup_c23 t))
let insert_fixup_c23_post_balance pc t = insert_fixup_c23_sorted t;
  match t with
  // case 2
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 d -> ()
   | Node Black a v1 (Node Red (Node Red b v2 c) v3 d) -> ()
  // case 3
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 d -> ()
   | Node Black a v1 (Node Red b v2 (Node Red c v3 d)) -> ()

val insert_fixup : pc:colour -> t:tree {pre_balance pc t} 
                   -> Tot (t':tree {post_balance pc t'
		     /\ (forall x. gmember t x <==> gmember t' x)
		     /\ black_height t == black_height t'})
let insert_fixup pc t = match t with
  // red-red
   | Node Red (Node Red a _ b) _ c -> assert (ired_red t); t
   | Node Red a _ (Node Red b _ c) -> assert (ired_red t); t
  // case 1
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 (Node Red d v4 e)
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 (Node Red d v4 e)
   | Node Black (Node Red a v1 b) v2 (Node Red (Node Red c v3 d) v4 e)
   | Node Black (Node Red a v1 b) v2 (Node Red c v3 (Node Red d v4 e)) ->
      insert_fixup_c1_height t;
      insert_fixup_c1_member t;
      insert_fixup_c1_post_balance pc t;
      insert_fixup_c1_sorted t;
      insert_fixup_c1 t
  // case 2
   | Node Black (Node Red a v1 (Node Red b v2 c)) v3 d
   | Node Black a v1 (Node Red (Node Red b v2 c) v3 d) ->
      insert_fixup_c23_heigth t;
      insert_fixup_c23_member t;
      insert_fixup_c2_sorted t;
      insert_fixup_c23_post_balance pc t;
      insert_fixup_c23 t
  // case 3
   | Node Black (Node Red (Node Red a v1 b) v2 c) v3 d
   | Node Black a v1 (Node Red b v2 (Node Red c v3 d)) ->
      insert_fixup_c23_heigth t;
      insert_fixup_c23_member t;
      insert_fixup_c3_sorted t;
      insert_fixup_c23_post_balance pc t;
      insert_fixup_c23 t
  // nothing to do
   | Node Red a _ b -> t
   | Node Black a _ b -> t
   | Leaf -> Leaf

val child_colour : colour -> colour -> GTot bool
let child_colour pc c = match pc,c with
  | Red,Red -> false
  | _ -> true

val insert_help_l0 : v:int -> ppc: colour -> pc:colour {child_colour ppc pc} 
                   -> t1:tree {post_balance pc t1 
		        /\ (Node? t1 ==> v > max_elem t1)} 
		   -> t2:tree { is_srbtree t2
			/\ child_colour pc (get_rcol t2)
		        /\ (Node? t2 ==> v < min_elem t2)
			/\ black_height t1 = black_height t2} 
		   -> Lemma (pre_balance ppc (Node pc t1 v t2))
let insert_help_l0 v ppc pc t1 t2 = let n = Node pc t1 v t2 in
 match n with
   | Node Red (Node Red a _ b) _ c -> assert (ired_red n)
   | Node Black (Node Red (Node Red a _ b) _ c) _ (Node Red d _ e) -> ()
   | Node Black (Node Red a _ (Node Red b _ c)) _ (Node Red d _ e) -> ()
   | Node Black (Node Red (Node Red a _ b) _ c) _ d -> ()
   | Node Black (Node Red a _ (Node Red b _ c)) _ d -> ()
   | Node Red a _ b -> ()
   | Node Black a _ b -> ()

val insert_help_r0 : v:int -> ppc: colour -> pc:colour {child_colour ppc pc} 
		   -> t1:tree { is_srbtree t1
			/\ child_colour pc (get_rcol t1)
		        /\ (Node? t1 ==> v > max_elem t1)} 
                   -> t2:tree {post_balance pc t2 
		        /\ (Node? t2 ==> v < min_elem t2)
			/\ black_height t1 = black_height t2} 
		   -> Lemma (pre_balance ppc (Node pc t1 v t2))
let insert_help_r0 v ppc pc t1 t2 = let n = Node pc t1 v t2 in
  match n with
  | Node Red a _ (Node Red b _ c) -> assert (ired_red n)
  | Node Black (Node Red a _ b) _ (Node Red (Node Red c _ d) _ e) -> assert (icase1 n)
  | Node Black (Node Red a _ b) _ (Node Red c _ (Node Red d _ e)) -> assert (icase1 n)
  | Node Black a _ (Node Red (Node Red b _ c) _ d) -> assert (icase2 n)
  | Node Black a _ (Node Red b _ (Node Red c _ d)) -> assert (icase3 n)
  | Node Red a _ b -> assert (is_srbtree n)
  | Node Black a _ b -> assert (is_rbtree n)

val insert0 : pc: colour -> x:int
  -> t:tree{is_srbtree t /\ child_colour pc (get_rcol t)} 
  -> Tot (t':tree {post_balance pc t' 
       /\ (forall z. gmember t' z <==> z==x \/ gmember t z)
       /\ black_height t == black_height t'
       /\ (Node? t ==> max_elem t' == max x (max_elem t)
       /\ min_elem t' == min x (min_elem t))
       /\ (Leaf? t ==> max_elem t' == x /\ min_elem t' == x)})
			       (decreases t)
let rec insert0 pc x t = match t with
  | Leaf -> Node Red Leaf x Leaf
  | Node c a v b -> if x < v
		     then let a' = insert0 c x a in
		     insert_help_l0 v pc c a' b;
		     let t0 = Node c a' v b in
		     max_elem_max' t;
		     let res = insert_fixup pc t0 in
		     max_transform t0 res;
		     min_transform t0 res;
		     res
		   else if v < x
		     then let b' = insert0 c x b in
		     insert_help_r0 v pc c a b';
		     let t0 = Node c a v b' in
		     min_elem_min' t;
		     let res = insert_fixup pc t0 in
		     max_transform t0 res;
		     min_transform t0 res;
		     res
		   else (
		     assert (v == x);
		     max_elem_max' t;
		     min_elem_min' t;
		     t
		   )

val insert : x:int -> t:tree {is_rbtree t} ->
  Tot (t':tree {is_rbtree t' /\ (forall z. gmember t z ==> gmember t' z)
    /\ (forall z. gmember t' z ==> z == x \/ gmember t z)
    /\ gmember t' x})
let insert x t = let t' = insert0 Red x t in
   match t' with
    | Node Red a v b -> Node Black a v b
    | _ -> t'
