import PolyML.Monoidal.Fin
import PolyML.Monoidal.FreeCommMon
import PolyML.ForMathlib.Monoidal.Semiring

namespace CategoryTheory

open Category CategoryTheory NNO Functor MonoidalCategory Mon_Class Limits CommMon ListArithmetic

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  [NNO C] [HasPullbacks C] [HasBinaryCoproducts C] [WithBags C] [ListArithmetic C] [ChosenPullbacks C]

variable {I O E B : C}

structure PolyCat where
  i : E ⟶ I
  o : B ⟶ O
  p : E ⟶ B
  [finFibres : FiniteFibres p]

-- Make the instance available
attribute [instance] PolyCat.finFibres

namespace PolyCat

variable (pol : PolyCat (C:=C) (I:=I) (O:=O) (E:=E) (B:=B))

variable {S : Semiring C}

def pullback (m : I ⟶ S.X) : E ⟶ S.X := pol.i ≫ m

def list_aggregator : list S.X ⟶ S.X := Mon.aggregator { X := S.X }

def bag_map (m : E ⟶ S.X) : bag E ⟶ bag S.X := bag.map m

def list_map (m : E ⟶ S.X) : list E ⟶ list S.X := list.map m

end PolyCat

end CategoryTheory
