import PolyML.Monoidal.Fin
import PolyML.Monoidal.FreeCommMon
import PolyML.ForMathlib.Monoidal.Semiring

-- import PolyML.Monoidal.ListArithmetic
-- import PolyML.Monoidal.FreeMon

namespace CategoryTheory

open Category CategoryTheory NNO Functor MonoidalCategory Mon_Class Limits CommMon ListArithmetic

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  [NNO C] [HasPullbacks C] [HasBinaryCoproducts C] [WithBags C] [ListArithmetic C]

variable {I O E B : C}

structure PolyCat where
  i : E ⟶ I
  o : B ⟶ O
  p : E ⟶ B
  [finFibres : HasFiniteFibres p]

-- Make the instance available
attribute [instance] PolyCat.finFibres

namespace PolyCat

variable (pol : PolyCat (C:=C) (I:=I) (O:=O) (E:=E) (B:=B))

variable {S : Semiring C}

def pullback (m : I ⟶ S.X) : E ⟶ S.X := pol.i ≫ m

def list_aggregator : list S.X ⟶ S.X := Mon.aggregator { X := S.X }

--def bag_of_m (m : E ⟶ S.X) := bag.map m ≫ bag.aggregator

-- -- def pushforward (m : E ⟶ S.X) : B ⟶ S.X :=
-- --    _ |> bag.map m |> bag.aggregator
-- --   --_ |> list.map m |> bag.aggregator

-- /--
-- This morphism represents the dependent function which, for each "point" `b : 1 ⟶ B`,
-- collects the "values" of `m` over the fiber `p⁻¹(b)` into a "list"
-- (a free monoid element).

-- In the `Type` version, this is `fun b => (listOfFinEnumFibres p b) |> List.map m`.
-- This is a dependent map `B → List R`.

-- Defining this morphism `B ⟶ list S.X` requires "integrating"
-- or "pushing forward" the `FinEnum` structure along `p` to construct a
-- `list S.X` for each fiber, which requires dependent products/types
-- not fully defined in your files.
-- -/
-- noncomputable def push_to_list (m : E ⟶ S.X) : B ⟶ list S.X :=
--   sorry -- This definition requires dependent products/fiberwise list construction

-- /--
-- Categorical pushforward operation.
-- This is the analogue of `fun b => ... |> aggregate`.

-- It's defined by first pushing the values of `m` in each fiber into a `list`
-- (using `push_to_list`), and then applying the `list_aggregator` morphism
-- (which corresponds to `List.foldr (*) 1`) to compute the multiplicative
-- product in each fiber.
-- -/
-- noncomputable def pushforward (m : E ⟶ S.X) : B ⟶ S.X :=
--   push_to_list pol m ≫ list_aggregator (S:=S)

-- -- The `pushdown` operation from your `Type` file (commented out)
-- -- would be:
-- def pushdown (m : B ⟶ S.X) : E ⟶ S.X :=
--   pol.p ≫ m

end PolyCat

end CategoryTheory
