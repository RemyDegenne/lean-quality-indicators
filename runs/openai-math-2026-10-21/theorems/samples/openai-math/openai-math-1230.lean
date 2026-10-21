namespace OAI

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace ContinuumCoulomb

theorem repulsionMultiplier_add {n : ℕ} (u v : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    repulsionMultiplier (u.add v) s = repulsionMultiplier u s+repulsionMultiplier v s := by
  apply Lp.ext
  filter_upwards [(repulsion_mul_memLp (u.add v) s).coeFn_toLp,
    (repulsion_mul_memLp u s).coeFn_toLp,(repulsion_mul_memLp v s).coeFn_toLp,
    Lp.coeFn_add (repulsionMultiplier u s) (repulsionMultiplier v s)] with x huv hu hv ha
  change repulsionMultiplier (u.add v) s x = _ at huv
  change repulsionMultiplier u s x = _ at hu
  change repulsionMultiplier v s x = _ at hv
  rw [ha]
  simp only [Pi.add_apply]
  rw [hu,hv,huv]
  change (repulsionPotential x:ℂ)*(u.value s x+v.value s x) = _
  exact mul_add _ _ _

end ContinuumCoulomb
end
end OAI
