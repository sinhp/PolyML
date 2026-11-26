import PolyML.Monoidal.WithPListListArithmetic
import PolyML.Monoidal.Vect

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.PList CategoryTheory.plist

section test1
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [WithPList C]
variable {A P Y : C}

#check withPList_cmp_eq_associator
#check plist.rc_uniq
#check plist.cmp
#check PList.ofPList.freeActionFunctor_forget_obj
#check PList.ofPList.freeForgetAdj_unit_app
#check PList.ofPList.withRecursionOfPList.freeActionFunctor_obj_str

example : plist.cmp A P Y = (α_ (PList.L A) P Y).inv := by
  refine (plist.rc_uniq (r := (α_ (PList.L A) P Y).inv) ?_ ?_).symm
  · sorry
  · sorry

end test1

section test2
variable {k : Type u} [Field k]
variable {V P B : CategoryTheory.Vect k}
variable {f : P ⟶ B} {g : V ⊗ B ⟶ B}
open CategoryTheory.Vect CategoryTheory.ModuleCat.MonoidalCategory

#check cons_prc_proof
#check prc_uniq_proof

end test2
