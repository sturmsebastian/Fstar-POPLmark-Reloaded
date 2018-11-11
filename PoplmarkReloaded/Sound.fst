module Sound

open FStar.List.Tot
open FStar.Constructive
open Prelude
open Base
open PropSN

type sSNe (g:ctx): t:ty -> e:texp g t -> Type =
  | SNeVar: v:var {v < length g} ->
	    sSNe g (index g v) (TyVar v)
  | SNeApp: #t1:ty ->
	    #t2:ty ->
	    #e1:texp g (TArr t1 t2) ->
	    #e2:texp g t1 ->
	    hsne:sSNe g (TArr t1 t2) e1 ->
	    hsn:sSN g t1 e2 ->
	    sSNe g t2 (TyApp e1 e2)
and sSN (g:ctx): t:ty -> e:texp g t -> Type =
  | SNLam: tlam:ty ->
	   #t:ty ->
	   #e:texp (tlam::g) t ->
	   hsn:sSN (tlam::g) t e ->
	   sSN g (TArr tlam t) (TyLam tlam e)
  | SNNeut: #t:ty ->
	    #e:texp g t ->
	    hsne:sSNe g t e ->
	    sSN g t e
  | SNStep: #t:ty ->
	    #e1:texp g t ->
	    #e2:texp g t ->
	    snstep:sSN_head_red g t e1 e2 ->
	    hsn:sSN g t e2 ->
	    sSN g t e1
and sSN_head_red (g:ctx): t:ty -> e1:texp g t -> e2:texp g t -> Type =
  | SNHBeta: #tlam:ty ->
	     #t:ty ->
	     #e1:texp g tlam ->
	     e2:texp (tlam::g) t ->
	     hsn:sSN g tlam e1 ->
	     sSN_head_red g t (TyApp (TyLam tlam e2) e1)
	       (subst (sub_beta e1) e2)
  | SNHApp: #t1:ty ->
	    #t2:ty ->
	    #e1:texp g (TArr t1 t2) ->
	    #e1':texp g (TArr t1 t2) ->
	    hshr:sSN_head_red g (TArr t1 t2) e1 e1' ->
	    e2:texp g t1 ->
	    sSN_head_red g t2 (TyApp e1 e2) (TyApp e1' e2)
	    
// Lemma 2.15
val ne_if_SNe: #g:ctx -> #t:ty -> #e:texp g t
  -> hsne:sSNe g t e -> Tot (ne g t e)
  (decreases hsne)
let rec ne_if_SNe #g #t #e hsne = match hsne with
  | SNeVar #g v -> NeVar #g v
  | SNeApp #_ #_ #_ #_ #e2 hsne hsn -> let hne = ne_if_SNe hsne in
    NeApp hne e2

// Lemma 2.16
val sound_SN: #g:ctx -> #t:ty -> #e:texp g t -> hsn:sSN g t e -> 
  Tot (n:nat & ssn n g t e)
  (decreases hsn)
val sound_SNe: #g:ctx -> #t:ty -> #e:texp g t -> hsne:sSNe g t e ->
  Tot (n:nat & ssn n g t e)
  (decreases hsne)
val sound_SN_head_red: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t
  -> hshr:sSN_head_red g t e1 e2 -> Tot (ssn_head_red g t e1 e2)
  (decreases hshr)
let rec sound_SN #g #t #e hsn = match hsn with
  | SNLam tlam hsn' -> let Mkdtuple2 n ssn' = sound_SN hsn' in
    Mkdtuple2 n (sn_lam tlam ssn')
  | SNNeut hsne -> sound_SNe hsne
  | SNStep snstep hsn -> let Mkdtuple2 n ssn = sound_SN hsn in
    let hshr = sound_SN_head_red snstep in
    back_closed_sn hshr ssn 
and sound_SNe #g #t #e hsne = match hsne with
   | SNeVar #g v -> Mkdtuple2 1 (sn_vars 0 g v)
   | SNeApp hsne hsn -> let Mkdtuple2 n1 ssn1 = sound_SNe hsne in
     let Mkdtuple2 n2 ssn2 = sound_SN hsn in
     let ne1 = ne_if_SNe hsne in
     Mkdtuple2 (1+n1+n2) (ne_app_sn ne1 ssn1 ssn2)
and sound_SN_head_red #g #t #e1 #e2 hshr = match hshr with
  | SNHBeta e2 hsn -> let Mkdtuple2 _ ssn = sound_SN hsn in
    SsnHBeta e2 ssn
  | SNHApp hshr e2 -> let hshr' = sound_SN_head_red hshr in
    SsnHApp hshr' e2
