import Mathlib.CategoryTheory.ChosenFiniteProducts
import Lean
import Lean.Parser.Basic

section Category

open CategoryTheory

variable {C : Type*} [Category C]
variable {a b r : C}

def Port (r a : C) := r ⟶ a

def encode {a b : C} (f : a ⟶ b) : Port r a → Port r b := fun g => g ≫ f
def decode (f : ∀ {r : C}, Port r a → Port r b) : a ⟶ b := f (CategoryStruct.id a)

instance [Category C'] {x y : C'} : CoeFun (x ⟶ y) (fun _ => forall {r'}, Port r' x → Port r' y) where
  coe f := encode f

end Category

section Cartesian

open CategoryTheory MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C]
variable {r a b c : C}

def fst : Port r (a ⊗ b) → Port r a := encode (ChosenFiniteProducts.fst a b)
def snd : Port r (a ⊗ b) → Port r b := encode (ChosenFiniteProducts.snd a b)

def split (p : Port r (a ⊗ b)) : (Port r a × Port r b) := (fst p, snd p)
def pair' : Port r a × Port r b -> Port r (a ⊗ b) := ChosenFiniteProducts.lift.uncurry

open Lean Lean.Expr Lean.Meta

declare_syntax_cat split
syntax binderIdent : split
syntax split "," split : split
syntax "(" split ")" : split
syntax "[split|" split "]" : term
syntax "[tup|" split "]" : term

macro_rules
  | `([split| $_:binderIdent]) => `(id)
  | `([split| $a:split, $b:split]) => `(Prod.map [split|$a] [split|$b] ∘ split)
  | `([split| ($a:split)]) => `([split|$a])
  | `([tup| $a:ident]) => `($a)
  | `([tup| $_:hole]) => `(_)
  | `([tup| $a:split, $b:split]) => `(([tup|$a], [tup|$b]))
  | `([tup| ($a:split)]) => `([tup|$a])

open Parser Term

syntax "let'" split ":=" term ";" : term

macro_rules
  | `(let' $a:split := $b:term; $c:term) => `(let [tup|$a] := [split|$a] $b; $c)

syntax "fun'" split "=>" term : term

macro_rules
  | `(fun' $a:split => $b:term) => `(decode $ fun p => let' $a := p; $b)

class HasInputType (C' : Type*) (α : Type*) where
  toInputType : C'

instance [Category C'] {r a : C'} : HasInputType C' (Port r a) where
  toInputType := a

instance [Category C'] [MonoidalCategory C'] [i1 : HasInputType C' A] [i2 : HasInputType C' B] : HasInputType C' (A × B) where
  toInputType := i1.toInputType ⊗ i2.toInputType

class PairClass (C' : outParam Type*) [Category C'] (r : outParam C') (α : Type) [i : HasInputType C' α] where
  pair : α → Port r i.toInputType

instance [Category C'] {r a : C'} : PairClass C' r (Port r a) where
  pair := id

instance [Category C'] [ChosenFiniteProducts C'] {r : C'} [it1 : HasInputType C' A] [it2 : HasInputType C' B] [i1 : PairClass C' r A] [i2 : PairClass C' r B] : PairClass C' r (A × B) where
  pair := fun (x,y) => pair' (i1.pair x, i2.pair y)

instance : Coe (Port r a) (Port r a) where
 coe := id

instance [Coe A (Port r a)] [Coe B (Port r b)] : Coe (A × B) (Port r (a ⊗ b))
  where
    coe := fun ⟨a, b⟩ => pair' (a,b)

end Cartesian

section Examples

open CategoryTheory MonoidalCategory PairClass

variable [Category D]
variable {a b c d : D}

def comp (f : b ⟶ c) (g : a ⟶ b) : a ⟶ c := fun' x => f (g x)

variable [Category C] [ChosenFiniteProducts C]
variable {a b c d : C}

def fst' : a ⊗ b ⟶ a := fun' (a,_) => a
def snd' : a ⊗ b ⟶ b := fun' (_,b) => b

def swap : a ⊗ b ⟶ b ⊗ a := fun' (a,b) => (b,a)

def reverse3 : a ⊗ b ⊗ c ⟶ c ⊗ b ⊗ a := fun' (x,y,z) =>
  let' (y',x') := swap (pair (x,y));
  (z,y',x')

def reverse4 : a ⊗ b ⊗ c ⊗ d ⟶ d ⊗ c ⊗ b ⊗ a := fun' (x,y,z,w) =>
  let t := reverse3 (pair (x,y,z))
  (w,t)

end Examples
