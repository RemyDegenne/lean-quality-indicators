@[expose] public section

open Fin Function Finset

universe uR uS uι uι' v v' v₁ v₂ v₃

variable {R : Type uR} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M' : Type v'}

open MultilinearMap

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable (R M M₂)

variable {R M M₂}

variable (R M M₂)

variable {R M M₂}

/-- Interpret a multilinear map in `n + 1` variables
as a linear map in `p`th variable with values in the multilinear maps in the other variables. -/
@[simps!]
def MultilinearMap.curryMid (p : Fin (n + 1)) (f : MultilinearMap R M M₂) :
    M p →ₗ[R] MultilinearMap R (fun i ↦ M (p.succAbove i)) M₂ where
  toFun x := .mk' fun m ↦ f (p.insertNth x m)
  map_add' x y := by ext; simp [map_insertNth_add]
  map_smul' c x := by ext; simp [map_insertNth_smul]

end
