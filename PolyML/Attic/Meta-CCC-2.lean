import Mathlib.CategoryTheory.Closed.Cartesian

section
open CategoryTheory ChosenFiniteProducts MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] [CartesianClosed C] {X Y Z : C}

def CategoryTheory.CartesianClosed.uncurryHom : (Y ⟹ X ⟹ Z) ⟶ (X ⊗ Y ⟹ Z) :=
  CartesianClosed.curry ((α_ _ _ _).hom ≫ CartesianClosed.uncurry (CartesianClosed.uncurry (𝟙 _)))

def CategoryTheory.CartesianClosed.applyMapHom : X ⟹ Y ⟹ Z ⟶ (X ⟹ Y) ⟹ X ⟹ Z :=
  CartesianClosed.curry
    (CartesianClosed.curry
      (lift
        (lift (fst ..) (snd .. ≫ fst ..))
        (lift (fst ..) (snd .. ≫ snd ..)) ≫
      (CartesianClosed.uncurry (𝟙 _) ⊗ CartesianClosed.uncurry (𝟙 _)) ≫
        CartesianClosed.uncurry (𝟙 _)))

def CategoryTheory.CartesianClosed.constLeft (m : X ⟶ Z) : X ⟶ Y ⟹ Z :=
  CartesianClosed.curry (snd Y X ≫ m)

def CategoryTheory.CartesianClosed.constRight (m : Y ⟶ Z) : X ⟶ Y ⟹ Z :=
  CartesianClosed.curry (fst Y X ≫ m)

def CategoryTheory.CartesianClosed.funOfHom {W : C} (f : (W ⟹ X) ⟶ (Y ⟹ Z)) (x : W ⟶ X) : Y ⟶ Z :=
  lift (𝟙 Y) (constRight x) ≫ CartesianClosed.uncurry f

end

declare_syntax_cat efun

namespace efun

open Lean Macro Elab CategoryTheory CartesianClosed

syntax:max (name := eof) "~" term:max : efun
syntax:max (name := eid) ident : efun
syntax (name := eparen) "(" efun ")" : efun
syntax:max (name := eabst) "funₑ" explicitBinders "=>" efun : efun
syntax:lead (name := eapp) efun:max efun:arg+ : efun
syntax:max (name := eto) "~" efun:max : term

@[macro eto]
partial def flattenSearch : Macro := fun stx => match stx with
  | `(term| ~$t) => do
    let (u, t) ← search t
    unless u do throwUnsupported
    `(term| ~$t)
  | _ => throwUnsupported
where
  search (stx : TSyntax `efun) : MacroM (Bool × TSyntax `efun) := match stx with
    | `(efun| $f $[$xs]* $y $z) => do
      let stx ← `(efun| ($f $[$xs]* $y) $z)
      let (_, stx) ← search stx
      return (true, stx)
    | `(efun| $f $x) => do
      let (u, f) ← search f
      let (v, x) ← search x
      let res ← `(efun| $f $x)
      return (u || v, res)
    | `(efun| funₑ%$tk $binders => $x) => do
      let (u, x) ← search x
      let res ← `(efun| funₑ%$tk $binders => $x)
      return (u, res)
    | `(efun| ($t)) => do
      let (_, t) ← search t
      return (true, t)
    | _ => pure (false, stx)

@[macro eto]
partial def expandBindersSearch : Macro := fun stx => match stx with
  | `(term| ~$t) => do
    let (u, t) ← search t
    unless u do throwUnsupported
    `(term| ~$t)
  | _ => throwUnsupported
where
  search (stx : TSyntax `efun) : MacroM (Bool × TSyntax `efun) := do
    let (u, stx) ← expandBinders stx
    match stx with
    | `(efun| $f $x) => do
      let (v, f) ← search f
      let (w, x) ← search x
      let res ← `(efun| $f $x)
      return (u || v || w, res)
    | `(efun| funₑ $binders => $x) => do
      let (v, x) ← search x
      let res ← `(efun| funₑ $binders => $x)
      return (u || v, res)
    | _ => pure (u, stx)
  expandBinders (stx : TSyntax `efun) : MacroM (Bool × TSyntax `efun) := match stx with
  | `(efun| funₑ%$tk $[$xs:binderIdent]* => $b) =>
    Prod.mk true <$> `(efun| funₑ%$tk ($[$xs:binderIdent]* : _) => $b)
  | `(efun| funₑ%$tk $[$xs:binderIdent]* : $t => $b) =>
    Prod.mk true <$> `(efun| funₑ%$tk ($[$xs:binderIdent]* : $t) => $b)
  | `(efun| funₑ%$tk $[$xs]* $y $z => $b) =>
    Prod.mk true <$> `(efun| funₑ%$tk $[$xs]* $y => funₑ%$tk $z:bracketedExplicitBinders => $b)
  | `(efun| funₑ%$tk ($[$xs]* $y $z : $t) => $b) =>
    Prod.mk true <$> `(efun| funₑ%$tk ($[$xs]* $y : $t) => funₑ%$tk ($z : $t) => $b)
  | _ => pure (false, stx)

@[macro eto]
partial def elabAbstSearch : Macro := fun stx => match stx with
  | `(term| ~$t) => do
    let (u, t) ← search t
    unless u do throwUnsupported
    `(term| ~$t)
  | _ => throwUnsupported
where
  search (stx : TSyntax `efun) : MacroM (Bool × TSyntax `efun) := do
    let (u, stx) ← elabAbst stx
    match stx with
    | `(efun| $f $x) => do
      let (v, f) ← search f
      let (w, x) ← search x
      let res ← `(efun| $f $x)
      return (u || v || w, res)
    | `(efun| funₑ $binders => $x) => do
      let (v, x) ← search x
      let res ← `(efun| funₑ $binders => $x)
      return (u || v, res)
    | _ => pure (u, stx)
  elabAbst (stx : TSyntax `efun) : MacroM (Bool × TSyntax `efun) := match stx with
  | `(efun| funₑ%$tk ($x : $t) => $f $y) =>
    Prod.mk true <$>
      `(efun| ~$(mkCIdentFrom tk ``applyMapHom) (funₑ ($x : $t) => $f) (funₑ ($x : $t) => $y))
  | `(efun| funₑ%$tk ($_x : $t) => ~$b) =>
    Prod.mk true <$> `(efun| ~(@$(mkCIdentFrom tk ``constRight) _ _ _ _ $t _ _ $b))
  | _ => pure (false, stx)

macro_rules
  | `(term| ~$t) => match t with
    | `(efun| ~$t) =>
      `(term| $t)
    | `(efun| $f $x) => `(term| $(mkCIdentFrom t ``funOfHom) ~$f ~$x)
    | `(efun| $i:ident) => `(term| $i)
    | `(efun| ($t)) => `(term| ~$t)
    | _ => throwUnsupported

@[macro eto]
partial def efunTelescope : Macro := fun stx => match stx with
  | `(term| ~$t) => push t #[]
  | _ => throwUnsupported
where
  push (stx : TSyntax `efun) (acc : Array (Option (TSyntax `ident) × TSyntax `term × Syntax)) :
      MacroM (TSyntax `term) :=
    match stx with
    | `(efun| funₑ%$tk ($x:ident : $t:term) => $b) => push b (acc.push (some x, t, tk))
    | `(efun| funₑ%$tk (_ : $t:term) => $b) => push b (acc.push (none, t, tk))
    | `(efun| $i:ident) => do
      let mut res : Option (TSyntax `term) := none
      let mut escStack : Array (TSyntax `term × Syntax) := #[]
      for j in acc.reverse do
        match j.fst with
        | some n =>
          if h : res.isSome then
            let b := res.get h
            res := some (← `(term| @$(mkCIdentFrom j.snd.snd ``constRight) _ _ _ _ $j.snd.fst _ _ $b))
          else if i.getId == n.getId then
            let mut st : TSyntax `term ← `(term| $(mkCIdentFrom i ``CategoryStruct.id) $j.snd.fst)
            for m in escStack do
              st ← `(term| @$(mkCIdentFrom m.snd ``constLeft) _ _ _ _ $j.snd.fst $m.fst _ $st)
            res := some st
          else
            escStack := escStack.push j.snd
        | none =>
          escStack := escStack.push j.snd
      match res with
      | some t => return t
      | none =>
        let mut fold : TSyntax `efun ← `(efun| ~$i)
        for j in acc.reverse do
          match j.fst with
          | some n =>
            fold ← `(efun| funₑ%$j.snd.snd ($n:ident : $j.snd.fst) => $fold)
          | none =>
            fold ← `(efun| funₑ%$j.snd.snd (_ : $j.snd.fst) => $fold)
        `(term| ~$fold)
    | _ => throwUnsupported

end efun

open CategoryTheory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] [CartesianClosed C] {X Y Z : C}

#check ~funₑ (g : Y ⟹ Z) (f : X ⟹ Y) (x : X) => g (f x)
