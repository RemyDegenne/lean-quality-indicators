public section

open Matrix UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm Manifold

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

lemma mdifferentiable_heckeSlashUpperTri {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (heckeSlashUpperTri k p f) := by
  rw [heckeSlashUpperTri_def]
  exact MDifferentiable.sum fun _ _ ↦ by
    rw [ModularForm.rat_slash]
    exact hf.slash k _

end HeckeRing.GL2
end
