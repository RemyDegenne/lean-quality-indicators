public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoTvAut

section Power

variable {K : Type} [Field K] {p : ℕ} [NeZero p]

variable {τ : Tag}

omit [NeZero p] in
theorem units_map_entrywise_eq_pow (σ : K →+* K) {m : ℕ}
    (hm : ∀ c : Kˣ, c ^ p = 1 → Units.map σ.toMonoidHom c = c ^ m) {v : ModGL τ K}
    (hv : v ∈ ExcFrames.splitPow τ K p) : Units.map (entrywiseHom σ) v = v ^ m := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hv.1
  have hbp : b ^ p = 1 :=
    rootDiagUnit_injective (by rw [← rootDiagUnit_pow, hv.2, rootDiagUnit_one])
  rw [rootDiagUnit_pow]
  refine Units.ext ?_
  change entrywise σ (rootDiag b) = rootDiag (b ^ m)
  rw [entrywise_rootDiag]
  congr 1
  funext i
  rw [hm (b i) (by simpa using congrFun hbp i), Pi.pow_apply]

end Power
end NoTvAut
end CFSG.StandardType
end
