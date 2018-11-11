module RBTreeDelete

open FStar.Math.Lib
open RBTree

type add_black_pos =
  | PosNone
  | PosSelf
  | PosLeft
  | PosRight

val is_root_pos: add_black_pos -> GTot bool
let is_root_pos = function
  | PosNone
  | PosSelf -> true
  | PosLeft
  | PosRight -> false

val dcase1l: tree -> GTot bool
let dcase1l t = match t with
  | Node Black ta _ (Node Red tc _ te) ->
     let l = black_height ta in
       is_rbtree ta && is_rbtree tc
       && is_rbtree te && sorted t
       && l+1 = black_height tc && l+1 = black_height te
  | _ -> false

val dcase2l : tree -> GTot bool
let dcase2l t = match t with
  | Node co ta _ (Node Black tc _ te) ->
      let l = black_height ta in
       is_rbtree ta && is_rbtree tc
       && is_rbtree te && sorted t
       && l = black_height tc && l = black_height te
  | _ -> false

val dcase3l : tree -> GTot bool
let dcase3l t = match t with
   | Node co ta _ (Node Black (Node Red c _ d) _ te) ->
     let l = black_height ta in
       is_rbtree ta && is_rbtree te
       && is_rbtree c && is_rbtree d
       && l = black_height te && sorted t
       && l = black_height c && l = black_height d
  | _ -> false

val dcase4l : tree -> GTot bool
let dcase4l t = match t with
  | Node co ta _ (Node Black tc _ (Node Red e _ f)) ->
     let l = black_height ta in
       is_rbtree ta && is_srbtree tc
       && is_srbtree e && is_srbtree f
       && l = black_height tc && sorted t
       && l = black_height e && l = black_height f
  | _ -> false

val dcase1r : tree -> GTot bool
let dcase1r t = match t with
 | Node Black (Node Red te _ tc) _ ta ->
     let l = black_height ta in
       is_rbtree ta && is_rbtree tc
       && is_rbtree te && sorted t
       && l+1 = black_height tc && l+1 = black_height te
  | _ -> false

val dcase2r : tree -> GTot bool
let dcase2r t = match t with
  | Node co (Node Black te _ tc) _ ta ->
      let l = black_height ta in
       is_rbtree ta && is_rbtree tc
       && is_rbtree te && sorted t
       && l = black_height tc && l = black_height te
  | _ -> false

val dcase3r : tree -> GTot bool
let dcase3r t = match t with
  | Node co (Node Black te _ (Node Red c _ d)) _ ta ->
     let l = black_height ta in
       is_rbtree ta && is_rbtree te
       && is_rbtree c && is_rbtree d
       && l = black_height te && sorted t
       && l = black_height c && l = black_height d
  | _ -> false

val dcase4r : tree -> GTot bool
let dcase4r t = match t with
  |Node co (Node Black (Node Red e _ f) _ tc) _ ta ->
     let l = black_height ta in
       is_rbtree ta && is_srbtree tc
       && is_srbtree e && is_srbtree f
       && l = black_height tc && sorted t
       && l = black_height e && l = black_height f
  | _ -> false

val post_fixup : sp:(tree * add_black_pos)  -> GTot bool
let post_fixup (t,p) = match p with
    | PosNone -> is_srbtree t
    | PosSelf -> is_rbtree t
    | _ -> false

val fixup_dcase4l : t:tree{dcase4l t}
        -> Tot (t':tree {sorted t' /\ red_black_childs t'
	/\ (forall x. gmember t x <==> gmember t' x)
        /\ (get_rcol t == Black ==> get_rcol t' == Black)})
let fixup_dcase4l = function
  | Node co ta v1 (Node Black tc v2 (Node Red e v3 f)) ->
     Node co (Node Black ta v1 tc) v2 (Node Black e v3 f)

val fixup_dcase4l_rbtree : t:tree{dcase4l t}
  -> Lemma (is_srbtree (fixup_dcase4l t)
  /\ black_height t == black_height (fixup_dcase4l t))
let fixup_dcase4l_rbtree t = match t with
  | Node co ta v1 (Node Black tc v2 (Node Red e v3 f)) -> ()

val fixup_dcase4r : t:tree{dcase4r t}
    -> Tot (t':tree {sorted t' /\ red_black_childs t'
    /\ (forall x. gmember t x <==> gmember t' x)
    /\ (get_rcol t == Black ==> get_rcol t' == Black)})
let fixup_dcase4r = function
  | Node co (Node Black (Node Red a v1 b) v2 tc) v3 ta ->
    Node co (Node Black a v1 b) v2 (Node Black tc v3 ta)

val fixup_dcase4r_rbtree: t:tree {dcase4r t}
  -> Lemma (is_srbtree (fixup_dcase4r t)
  /\ black_height t == black_height (fixup_dcase4r t))
let fixup_dcase4r_rbtree t = match t with
  | Node co (Node Black (Node Red a v1 b) v2 tc) v3 ta -> ()

val fixup_dcase3l : t:tree{dcase3l t}
               -> Tot (t':tree {sorted t' /\ red_black_childs t'
	       /\ (forall x. gmember t x <==> gmember t' x)
               /\ (get_rcol t == Black ==> get_rcol t' == Black)})
let fixup_dcase3l = function
   | Node co ta v1 (Node Black (Node Red c v2 d) v3 te) ->
     let t0 = Node co ta v1 (Node Black c v2 (Node Red d v3 te)) in
        assert (sorted t0);
	fixup_dcase4l t0

val fixup_dcase3l_rbtree: t:tree{dcase3l t}
  -> Lemma (is_srbtree (fixup_dcase3l t)
  /\ black_height t == black_height (fixup_dcase3l t))
let fixup_dcase3l_rbtree t = match t with
   | Node co ta v1 (Node Black (Node Red c v2 d) v3 te) -> ()

val fixup_dcase3r : t:tree{dcase3r t}
               -> Tot (t':tree {sorted t' /\ red_black_childs t'
	       /\ (forall x. gmember t x <==> gmember t' x)
               /\ (get_rcol t == Black ==> get_rcol t' == Black)})
let fixup_dcase3r = function
   | Node co (Node Black te v1 (Node Red c v2 d)) v3 ta ->
     let t' = Node co (Node Black (Node Red te v1 c) v2 d) v3 ta in
	assert (sorted t');
	fixup_dcase4r t'

val fixup_dcase3r_rbtree: t:tree{dcase3r t}
  -> Lemma (is_srbtree (fixup_dcase3r t)
  /\ black_height t == black_height (fixup_dcase3r t))
let fixup_dcase3r_rbtree t = match t with
   | Node co (Node Black te v1 (Node Red c v2 d)) v3 ta -> ()

val black_tree_pos_height: (tree * add_black_pos) -> GTot nat
let black_tree_pos_height (t, p) = match p with
  | PosLeft
  | PosRight
  | PosNone -> black_height t
  | PosSelf -> 1+black_height t

val fixup_dcase2l : t:tree{dcase2l t}
	-> Tot (tp':(tree * add_black_pos){
	  red_black_childs (fst tp')
	/\ (forall x. gmember t x <==> gmember (fst tp') x)
        /\ get_rcol (fst tp') == Black
        /\ (get_rcol t == Black ==> snd tp' == PosSelf)
	/\ (get_rcol t == Red ==> snd tp' == PosNone)})
let fixup_dcase2l = function
  | Node co ta v1 (Node Black tc v2 te) ->
    let p = if co = Red then PosNone else PosSelf in
    (Node Black ta v1 (Node Red tc v2 te), p)

val fixup_dcase2l_rbtree: t:tree{dcase2l t}
  -> Lemma (post_fixup (fixup_dcase2l t)
  /\ black_height t == black_tree_pos_height (fixup_dcase2l t))
let fixup_dcase2l_rbtree t = match t with
  | Node Red ta v1 (Node Black tc v2 te) -> ()
  | Node Black ta v1 (Node Black tc v2 te) -> ()

val fixup_dcase2r : t:tree{dcase2r t}
		 -> Tot (tp':(tree * add_black_pos) {
		   red_black_childs (fst tp')
		 /\ (forall x. gmember t x <==> gmember (fst tp') x)
                 /\ get_rcol (fst tp') == Black
                 /\ (get_rcol t == Black ==> snd tp' == PosSelf)
		 /\ (get_rcol t == Red ==> snd tp' == PosNone)})
let fixup_dcase2r = function
  | Node co (Node Black te v1 tc) v2 ta ->
    let p = if co = Red then PosNone else PosSelf in
     (Node Black (Node Red te v1 tc) v2 ta, p)

val fixup_dcase2r_rbtree: t:tree{dcase2r t}
  -> Lemma (post_fixup (fixup_dcase2r t)
    /\ black_height t == black_tree_pos_height (fixup_dcase2r t))
let fixup_dcase2r_rbtree t = ()

val pre_fixup : (tree * add_black_pos) -> GTot bool
let pre_fixup (t,p) = match p with
  | PosNone -> is_srbtree t
  | PosSelf -> is_srbtree t
  | PosLeft -> dcase1l t || dcase2l t
      || dcase3l t || dcase4l t
  | PosRight -> dcase1r t || dcase2r t
      || dcase3r t || dcase4r t

val casesl: t:tree -> GTot bool
let casesl t = match t with
  | Node Red l _ r -> 1+black_height l = black_height r
    && is_rbtree l && is_rbtree r && sorted t
  | Node Black l _ r -> 1+black_height l = black_height r
    && is_rbtree l && is_srbtree r && sorted t
  | _ -> false

val casesr: t:tree -> GTot bool
let casesr t = match t with
  | Node Red l _ r -> black_height l = 1+black_height r
    && is_rbtree l && is_rbtree r && sorted t
  | Node Black l _ r -> black_height l = 1+black_height r
    && is_srbtree l && is_rbtree r && sorted t
  | _ -> false

val is_casesl: t:tree
  -> Lemma (requires casesl t)
  (ensures dcase1l t \/ dcase2l t
	  \/ dcase3l t \/ dcase4l t)
let is_casesl t = match t with
  | Node Black ta _ (Node Red tc _ te) ->
    assert (dcase1l t);
    ()
  | Node co ta _ (Node Black _ _ (Node Red e _ f)) ->
    assert (dcase4l t);
    ()
  | Node co ta _ (Node Black (Node Red c _ d) _ te) ->
    assert (dcase3l t);
    ()
  | Node co ta _ (Node Black tc _ te) ->
    assert (dcase2l t);
    ()

val is_casesr: t:tree
  -> Lemma (requires casesr t)
    (ensures dcase1r t \/ dcase2r t
	  \/ dcase3r t \/ dcase4r t)
let is_casesr t = match t with
  | Node Black (Node Red te _ tc) _ ta ->
    assert (dcase1r t);
    ()
  | Node co (Node Black (Node Red e _ f) _ _) _ ta ->
    assert (dcase4r t);
    ()
  | Node co (Node Black te _ (Node Red c _ d)) _ ta ->
    assert (dcase3r t);
    ()
  | Node co (Node Black te _ tc) _ ta ->
    assert (dcase2r t);
    ()

let fst3 (a,_,_) = a
let snd3 (_,b,_) = b
let thd3 (_,_,c) = c

type dcase1l_helper0_t (t:tree) (t1:tree) (v:int) (t2:tree) =
  sorted t1 /\ sorted t2 /\ casesl t1
  /\ (forall x. gmember t x <==> gmember t1 x \/ x==v \/ gmember t2 x)
  /\ (if Node? t1 then v > max_elem t1 else true)
  /\ (if Node? t2 then v < min_elem t2 else true)
  /\ get_rcol t1 == Red /\ is_rbtree t2
  /\ black_height t == 1+black_height t1
  /\ black_height t == 1+black_height t2
  /\ pre_fixup (t1,PosLeft)

val dcase1l_helper0: t:tree{dcase1l t}
  -> Tot (tp:(tree * int * tree)
    {dcase1l_helper0_t t (fst3 tp) (snd3 tp) (thd3 tp)})
let dcase1l_helper0 t = match t with
  | Node Black ta v1 (Node Red tc v2 te) ->
     assert (black_height t >=  1+black_height ta);
     assert (black_height t == 1+black_height tc);
     assert (black_height t == 1+black_height te);
     assert (get_rcol ta == Black);
     assert (get_rcol tc == Black);
     let tx = Node Red ta v1 tc in
     assert (casesl tx);
     is_casesl tx;
     assert (dcase2l tx \/ dcase3l tx \/ dcase4l tx);
     (tx, v2, te)

type dcase1r_helper0_t (t:tree) (t1:tree) (v:int) (t2:tree) =
  sorted t1 /\ sorted t2 /\ casesr t2
  /\ (forall x. gmember t x <==> gmember t1 x \/ x==v \/ gmember t2 x)
  /\ (if Node? t1 then v > max_elem t1 else true)
  /\ (if Node? t2 then v < min_elem t2 else true)
  /\ get_rcol t2 == Red /\ is_rbtree t1
  /\ black_height t == 1+black_height t1
  /\ black_height t == 1+black_height t2
  /\ pre_fixup (t2, PosRight)

val dcase1r_helper0: t:tree{dcase1r t}
  -> Tot (tp:(tree * int * tree)
  {dcase1r_helper0_t t (fst3 tp) (snd3 tp) (thd3 tp)})
let dcase1r_helper0 t = match t with
  | Node Black (Node Red te v1 tc) v2 ta ->
     assert (black_height t >= 1+black_height ta);
     assert (black_height t == 1+black_height tc);
     assert (black_height t == 1+black_height te);
     let tx = Node Red tc v2 ta in
     assert (casesr tx);
     is_casesr tx;
     (te, v1, tx)

val dcase1_helper1: t1:tree {sorted t1 /\ red_black_childs t1}
 -> v:int {if Node? t1 then v > max_elem t1 else true}
 -> t2:tree {sorted t2 /\ red_black_childs t2
   /\ (if Node? t2 then v < min_elem t2 else true )}
 -> Tot (t':tree {sorted t' /\ red_black_childs t'
   /\ (forall x. gmember t' x <==> gmember t1 x \/ x==v \/ gmember t2 x)
   /\ get_rcol t' == Black})
let dcase1_helper1 t1 v t2 =
   let tx = Node Black t1 v t2 in
     assert (sorted tx);
     tx

val fixup_delete_spec : (tree * add_black_pos)
  -> (tree * add_black_pos) -> GTot bool
let fixup_delete_spec tp tp' =
 let t,p = tp in
 let t',p' = tp' in
  red_black_childs t' && sorted t'
  && (if p = PosLeft then (
    if dcase2l t && get_rcol t = Black then p' = PosSelf
    else p' = PosNone
  ) else if p = PosRight then (
    if dcase2r t && get_rcol t = Black then p' = PosSelf
    else p' = PosNone
  ) else p' = p || p' = PosNone
  ) && (if p' = PosSelf then get_rcol t' = Black else true)

#reset-options "--z3rlimit 10"

val fixup_dcase1l : t:tree{dcase1l t}
  -> Tot (t':tree {sorted t' /\ red_black_childs t'
    /\ (forall x. gmember t x <==> gmember t' x)
    /\ (get_rcol t == Black ==> get_rcol t' == Black)})
    (decreases %[black_height t; 0])
val fixup_dcase1r : t:tree{dcase1r t}
  -> Tot (t':tree {sorted t' /\ red_black_childs t'
  /\ (forall x. gmember t x <==> gmember t' x)
  /\ (get_rcol t == Black ==> get_rcol t' == Black)})
  (decreases %[black_height t; 0])
val fixup_delete : tp:(tree * add_black_pos) {pre_fixup tp}
  -> Tot (tp':(tree * add_black_pos) {
    fixup_delete_spec tp tp'
    /\ (forall x. gmember (fst tp) x <==> gmember (fst tp') x)
    /\ (get_rcol (fst tp) == Black ==> get_rcol (fst tp') == Black)})
  (decreases %[black_height (fst tp); 1])
let rec fixup_delete (t,p) = match t,p with
  | _, PosNone -> t, PosNone
  | Node Red l v r, PosSelf -> Node Black l v r, PosNone
  | _, PosSelf -> t,PosSelf
  // left cases
  | Node Black ta _ (Node Red tc _ te) ,PosLeft ->
    assert (dcase1l t);
    fixup_dcase1l t, PosNone
  | Node co ta _ (Node Black _ _ (Node Red e _ f)) ,PosLeft ->
    assert (~(dcase2l t));
    assert (~(dcase3l t));
    fixup_dcase4l t, PosNone
  | Node co ta _ (Node Black (Node Red c _ d) _ te) ,PosLeft ->
    assert (~(dcase4l t));
    assert (~(dcase2l t));
    fixup_dcase3l t, PosNone
  | Node co ta _ (Node Black tc _ te) ,PosLeft ->
    assert (~(dcase4l t));
    assert (~(dcase3l t));
    fixup_dcase2l t
  // right cases
  | Node Black (Node Red te _ tc) _ ta ,PosRight ->
    assert (dcase1r t);
    fixup_dcase1r t, PosNone
  | Node co (Node Black (Node Red e _ f) _ _) _ ta ,PosRight ->
    assert (~(dcase2r t));
    assert (~(dcase3r t));
    assert (dcase4r t);
    fixup_dcase4r t, PosNone
  | Node co (Node Black te _ (Node Red c _ d)) _ ta ,PosRight ->
    assert (~(dcase2r t));
    assert (~(dcase4r t));
    assert (dcase3r t);
    fixup_dcase3r t, PosNone
  | Node co (Node Black te _ tc) _ ta ,PosRight ->
    assert (~(dcase3r t));
    assert (~(dcase4r t));
    assert (dcase2r t);
    fixup_dcase2r t
and fixup_dcase1l t = match t with
  | Node Black ta v1 (Node Red tc v2 te) ->
     let (tx, v2', te') = dcase1l_helper0 t in
     is_casesl tx;
     assert (dcase1l tx \/ dcase2l tx \/ dcase3l tx \/ dcase4l tx);
     assert (pre_fixup (tx, PosLeft));
     let tx',p = fixup_delete (tx, PosLeft) in
     assert (p == PosNone);
     assert (sorted tx');
     min_transform tx tx';
     max_transform tx tx';
     dcase1_helper1 tx' v2' te'
and fixup_dcase1r t = match t with
  | Node Black (Node Red te v1 tc) v2 ta ->
     let (te', v1', tx) = dcase1r_helper0 t in
     is_casesr tx;
     assert (dcase1r tx \/ dcase2r tx \/ dcase3r tx \/ dcase4r tx);
     assert (pre_fixup (tx,PosRight));
     let tx', p = fixup_delete (tx, PosRight) in
     assert (sorted tx');
     assert (p == PosNone);
     min_transform tx tx';
     max_transform tx tx';
     dcase1_helper1 te' v1' tx'

#reset-options
 
val dcase1_helper1_rbtree: t1:tree -> v:int -> t2:tree
 -> Lemma (requires is_srbtree t1 /\ is_srbtree t2
   /\ black_height t1 == black_height t2
   /\ (if Node? t1 then v > max_elem t1 else true)
   /\ (if Node? t2 then v < min_elem t2 else true))
   (ensures is_srbtree (dcase1_helper1 t1 v t2)
    /\ 1+black_height t1 == black_height (dcase1_helper1 t1 v t2))
let dcase1_helper1_rbtree t1 v t2 = ()

val fixup_dcase1l_rbtree: t:tree
  -> Lemma (requires dcase1l t)
  (ensures is_srbtree (fixup_dcase1l t)
  /\ black_height t == black_height (fixup_dcase1l t))
  (decreases %[black_height t; 0])
val fixup_dcase1r_rbtree: t:tree
  -> Lemma (requires dcase1r t)
  (ensures is_srbtree (fixup_dcase1r t)
  /\ black_height t == black_height (fixup_dcase1r t))
  (decreases %[black_height t; 0])
val fixup_delete_rbtree: tp:(tree * add_black_pos)
  -> Lemma (requires pre_fixup tp)
  (ensures post_fixup (fixup_delete tp)
  /\ black_tree_pos_height tp == black_tree_pos_height (fixup_delete tp))
  (decreases %[black_height (fst tp); 1])
let rec fixup_delete_rbtree (t,p) = match t,p with
  | _, PosNone -> ()
  | Node Red l v r, PosSelf -> ()
  | _, PosSelf -> ()
  // left cases
  | Node Black ta _ (Node Red tc _ te) ,PosLeft ->
    fixup_dcase1l_rbtree t;
    ()
  | Node co ta _ (Node Black _ _ (Node Red e _ f)) ,PosLeft ->
    fixup_dcase4l_rbtree t;
    ()
  | Node co ta _ (Node Black (Node Red c _ d) _ te) ,PosLeft ->
    fixup_dcase3l_rbtree t;
    ()
  | Node co ta _ (Node Black tc _ te) ,PosLeft ->
    fixup_dcase2l_rbtree t;
    ()
  // right cases
  | Node Black (Node Red te _ tc) _ ta ,PosRight ->
    fixup_dcase1r_rbtree t;
    ()
  | Node co (Node Black (Node Red e _ f) _ _) _ ta ,PosRight ->
    fixup_dcase4r_rbtree t;
    ()
  | Node co (Node Black te _ (Node Red c _ d)) _ ta ,PosRight ->
    fixup_dcase3r_rbtree t;
    ()
  | Node co (Node Black te _ tc) _ ta ,PosRight ->
    fixup_dcase2r_rbtree t;
    ()
and fixup_dcase1l_rbtree t = match t with
  | Node Black ta v1 (Node Red tc v2 te) ->
     let (tx, v2', te') = dcase1l_helper0 t in
     assert (is_srbtree te');
     assert (black_height t == 1+black_height tx);
     assert (black_height t == 1+black_height te');
     let tx',p = fixup_delete (tx, PosLeft) in
     fixup_delete_rbtree (tx,PosLeft);
     assert (p == PosNone);
     assert (black_height tx' == black_height tx);
     assert (is_srbtree tx');
     dcase1_helper1_rbtree tx' v2' te';
     assert (black_height t == black_height (dcase1_helper1 tx' v2' te'))
and fixup_dcase1r_rbtree t = match t with
  | Node Black (Node Red te v1 tc) v2 ta ->
     let (te', v1', tx) = dcase1r_helper0 t in
     let tx', p = fixup_delete (tx, PosRight) in
     fixup_delete_rbtree (tx,PosRight);
     dcase1_helper1_rbtree te' v1' tx'

#reset-options "--z3rlimit 25"

val del_minimum: t:tree {is_srbtree t /\ Node? t}
  -> Tot (tp:(int * tree * add_black_pos) { post_fixup (snd3 tp,thd3 tp)
  /\ (forall z. gmember t z <==> (z == (fst3 tp) \/ gmember (snd3 tp) z))
  /\ black_height t == black_tree_pos_height (snd3 tp,thd3 tp)
  /\ (get_rcol t == Black ==> get_rcol (snd3 tp) == Black)
  /\ (if Node? (snd3 tp) then fst3 tp < min_elem (snd3 tp) else true)
  /\ (thd3 tp == PosSelf ==> get_rcol (snd3 tp) == Black)
  })
let rec del_minimum t = match t with
  | Node Red Leaf v r -> (v, r, PosNone)
  | Node Black Leaf v r -> let r',p' = fixup_delete (r, PosSelf) in
		      (v, r', p')
  | Node c l v r -> let vy, x, p = del_minimum l in
	     let tx = Node c x v r in
	     assert (vy < min_elem tx);
	     if Node? x then max_transform' x l
		else ();
	     assert (if Node? x then v > max_elem x else true);
	     assert (sorted tx);
	     assert (forall z. gmember t z <==> z == vy \/ gmember tx z);
	     assert (get_rcol t == Black ==> get_rcol tx == Black);
	     assert (red_black_childs tx);
	     assert (black_height t == black_height tx);
	     (match p with
	       | PosSelf -> assert (is_srbtree r);
		 assert (is_rbtree x);
		 assert (1+black_height x = black_height r);
		 assert (casesl tx);
		 is_casesl tx;
		 assert (pre_fixup (tx, PosLeft));
		 let tx', p' =  fixup_delete (tx, PosLeft) in
		 assert (forall z. gmember tx z <==> gmember tx' z);
		 assert (forall z. gmember t z <==> (z == vy \/ gmember tx' z));
		 assert (Node? tx');
		 min_transform tx tx';
		 assert (vy < min_elem tx');
		 assert (if Node? tx' then vy < min_elem tx' else true);
		 fixup_delete_rbtree (tx,PosLeft);
		 assert (post_fixup (tx', p'));
		 assert (black_tree_pos_height (tx,PosLeft) ==
		   black_tree_pos_height (tx',p'));
		 assert (black_height t == black_tree_pos_height (tx',p'));
		 assert (if get_rcol tx = Black then get_rcol tx' = Black
		   else true);
		 assert (get_rcol t == Black ==> get_rcol tx' == Black);
		 assert (p' == PosSelf ==> get_rcol tx' == Black);
		 (vy, tx', p')
	       | PosNone -> 
		 assert (black_height_correct tx);
		 assert (is_srbtree tx);
		 (vy, tx, p)
	      )

#reset-options

type delete1_t (t:tree) (t':tree) (p:add_black_pos) =
    Node? t /\ post_fixup (t',p)
    /\ black_height t == black_tree_pos_height (t',p)
    /\ (forall x. gmember t x <==> x == (Node?.v t) \/ (gmember t' x))
    /\ not (gmember t' (Node?.v t))
    /\ (get_rcol t == Black ==> get_rcol t' == Black)

val delete1_pre0: t:tree -> GTot bool
let delete1_pre0 t = match t with
  | Node _ _ _ (Node _ _ _ _) -> is_srbtree t
  | _ -> false

val sorted_gmember: c:colour -> l:tree -> v:int -> r:tree ->
  Lemma (requires sorted (Node c l v r))
  (ensures ~(gmember l v) /\ ~(gmember r v))
let sorted_gmember c l v r = 
  if Node? r then min_elem_min' r else ();
  if Node? l then max_elem_max' l else ()

#reset-options "--z3rlimit 25"

val delete1_help0: t:tree {delete1_pre0 t}
    -> Tot (tp:(tree * add_black_pos) {delete1_t t (fst tp) (snd tp)})
let delete1_help0 t = match t with
  | Node c l v r -> let vy,r',p = del_minimum r in
    let tx = Node c l vy r' in
    assert (get_rcol t == Black ==> get_rcol tx == Black);
    assert (sorted l);
    assert (sorted r');
    min_elem_min' r;
    assert (if Node? l then vy > max_elem l else true);
    assert (sorted tx);
    assert (red_black_childs tx);
    assert (black_height l == black_height r);
    assert (black_height r == black_tree_pos_height (r',p));
    sorted_gmember c l v r;
    assert (forall z. gmember r' z ==> gmember r z);
    assert (gmember r vy);
    assert (v <> vy);
    assert (~(gmember r' v));
    assert (not (gmember tx v));
    match p with
    | PosNone ->
      assert (black_height r == black_height r');
      assert (black_height_correct tx);
      assert (is_srbtree tx);
      assert (post_fixup (tx,PosNone));
      assert (black_height t == black_height tx);
      assert (black_height t == black_tree_pos_height (tx,PosNone));
      assert (forall z. gmember t z <==> z == v \/ gmember tx z);
      tx, PosNone
    | PosSelf -> 
      assert (black_height t == black_height tx);
      assert (black_height t == black_tree_pos_height (tx,PosRight));
      assert (is_rbtree r');
      (match c with
       | Red -> assert (is_rbtree l)
       | Black -> assert (is_srbtree l)
       );
      assert (casesr tx);
      is_casesr tx;
      assert (pre_fixup (tx,PosRight));
      fixup_delete_rbtree (tx, PosRight);
      let t',p' = fixup_delete (tx, PosRight) in
      assert (black_tree_pos_height (tx,PosRight)
	== black_tree_pos_height (t',p'));
      assert (get_rcol tx == Black ==> get_rcol t' == Black);
      assert (get_rcol t == Black ==> get_rcol t' == Black);
      assert (post_fixup (t',p'));
      assert (forall z. gmember t z <==> z == v \/ gmember t' z);
      assert (~(gmember t' v));
      t',p'

#reset-options

val delete1: t:tree {Node? t /\ is_srbtree t} -> Tot (tp:(tree * add_black_pos)
  {delete1_t t (fst tp) (snd tp)})
let delete1 t = match t with
  | Node Red Leaf _ r -> r,PosNone
  | Node Black Leaf _ r -> fixup_delete (r,PosSelf)
  | Node Red l _ Leaf -> l,PosNone
  | Node Black l _ Leaf -> fixup_delete (l,PosSelf)
  | Node c l _ r -> delete1_help0 t

val delete0al: l':tree {is_srbtree l'}
  -> p: add_black_pos{is_root_pos p /\ (p==PosSelf ==> get_rcol l' == Black)}
  -> c:colour {c==Red ==> get_rcol l' == Black}
  -> v:int {if Node? l' then v > max_elem l' else true}
  -> r:tree { is_srbtree r
	    /\ (if Node? r then v < min_elem r else true)
	    /\ black_height r == black_tree_pos_height (l',p)
	    /\ (c==Red ==> get_rcol r == Black) }
  -> Tot (tp:(tree * add_black_pos)
  { post_fixup tp
  /\ (c==Red==>black_height r == black_tree_pos_height tp)
  /\ (c==Black==>1+black_height r == black_tree_pos_height tp)
  /\ (forall y. gmember l' y \/ y==v \/ gmember r y <==> gmember (fst tp) y)
  /\ (c==Black ==> get_rcol (fst tp) == Black)})
let delete0al l' p c v r =
  let tx = Node c l' v r in
  match p with
  | PosNone -> tx, PosNone
  | PosSelf -> is_casesl tx;
	      fixup_delete_rbtree (tx,PosLeft);
	      fixup_delete (tx,PosLeft)

val delete0ar: l:tree {is_srbtree l}
  -> c:colour {c==Red ==> get_rcol l == Black}
  -> v:int {if Node? l then v > max_elem l else true}
  -> r':tree { is_srbtree r'
	    /\ (if Node? r' then v < min_elem r' else true)
	    /\ (c==Red ==> get_rcol r' == Black) }
  -> p: add_black_pos{is_root_pos p
            /\ (p==PosSelf ==> get_rcol r' == Black)
	    /\ black_height l == black_tree_pos_height (r',p)}
  -> Tot (tp:(tree * add_black_pos)
  { post_fixup tp
  /\ (c==Red==>black_height l == black_tree_pos_height tp)
  /\ (c==Black==>1+black_height l == black_tree_pos_height tp)
  /\ (forall y. gmember l y \/ y==v \/ gmember r' y <==> gmember (fst tp) y)
  /\ (c==Black ==> get_rcol (fst tp) == Black)})
let delete0ar l c v r' p = let tx = Node c l v r' in
  match p with
  | PosNone -> tx, PosNone
  | PosSelf -> is_casesr tx;
	      fixup_delete_rbtree (tx,PosRight);
	      fixup_delete (tx,PosRight)

#reset-options "--z3rlimit 10"

val delete0: x:int -> t:tree{is_srbtree t} ->
  Tot (tp:(tree * add_black_pos)
  { post_fixup tp
  /\ black_height t == black_tree_pos_height tp
  /\ (forall y. gmember t y ==> x == y \/ gmember (fst tp) y)
  /\ (forall y. gmember (fst tp) y ==> gmember t y)
  /\ not (gmember (fst tp) x)
  /\ (get_rcol t == Black ==> get_rcol (fst tp) == Black)})
let rec delete0 x t = match t with
  | Leaf -> Leaf, PosNone
  | Node c l v r ->
    if x = v then delete1 t
    else if x < v
     then ( let l',p = delete0 x l in
	if Node? r then min_elem_min' r else ();
	if Node? l' then max_transform' l' l else ();
	delete0al l' p c v r
     ) else ( let r',p = delete0 x r in
	if Node? l then max_elem_max' l else ();
	if Node? r' then min_transform' r' r else ();
	delete0ar l c v r' p
     )

#reset-options

val delete: x:int -> t:tree {is_rbtree t}
  -> Tot (t':tree { is_rbtree t'
  /\ (forall y. gmember t y ==> x == y \/ gmember t' y)
  /\ (forall y. gmember t' y ==> gmember t y)
  /\ not (gmember t' x) })
let delete x t = let t',_ = delete0 x t in
                   match t' with
		     | Leaf -> Leaf
		     | Node c l v r -> Node Black l v r


