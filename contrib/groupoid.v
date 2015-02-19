Require Import HoTT.

Record CategoryStruct {obj:hSet}{hom:obj -> obj ->hSet}
                     :Type:={
id:forall x, hom x x;
comp:forall {x y z}, hom y z -> hom x y -> hom x z}.

Record IsCategory (obj:hSet)(hom:obj -> obj ->hSet)
       (cs: @CategoryStruct obj hom) : Type := {
right_id: forall x y, forall f:hom x y, 
   (comp cs) f ((id cs) x) = f;
left_id: forall x y, forall f:hom x y, 
   comp cs (id cs y) f = f;
assoc: forall x y z w:obj, forall f:hom z w, 
       forall g:hom y z, forall h: hom x y,
   comp cs f (comp cs g h)= comp cs (comp cs f g) h
}.

Require Import Record.

(* Will need tactic issig3 and then equality on subset types *)

Lemma isprop_iscategory (O:hSet)(H:O->O->hSet)(cs:CategoryStruct):
   IsHProp (IsCategory O H cs).
