import PolyML.Monoidal.Vect
open CategoryTheory ModuleCat DirectSum TensorProduct
variable {k : Type u} [Field k] (V : Vect k) (P : Vect k) (a : k) (p : P.carrier)

example : SMul.smul a ((DirectSum.lof k ℕ V.listFamily 0) (1 : k)) ⊗ₜ[k] p =
    SMul.smul a ((DirectSum.lof k ℕ V.listFamily 0) (1 : k) ⊗ₜ[k] p) := by
  change (a • ((DirectSum.lof k ℕ V.listFamily 0) (1 : k))) ⊗ₜ[k] p =
      a • ((DirectSum.lof k ℕ V.listFamily 0) (1 : k) ⊗ₜ[k] p)
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
