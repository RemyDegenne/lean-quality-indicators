public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.LayerSixE
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem kgL3ii_clause {K : Type} [Field K] [Finite K] (h3ii : KGAdjL3ii)
    (hchar : ringChar K = 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (hF : KGAutFrame A κ) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hconj : ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))) * kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))))⁻¹)
    {a b : A} (hab : GGCorootOrth 3 (ggTorusAut A) a b) :
    ∀ u ∈ ggFixedByCentres 3 (ggTorusAut A) {a, b},
      ∃ l : L', ψ l ∈ (rootSpan Tag.E6 K (kgKernelE6
          {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
           kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})).comap (kgThetaHom g) ∧
        MulAut.conj l = (u : MulAut L') := by
  intro u hu
  obtain ⟨α, β, hα, hβ, hαβ, ha, hb⟩ := hF.corootOrth hab
  have hku := hF.fixedByCentres hα hβ hαβ ha hb hu
  have hdu : rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ u))) ∈
      rootSpan Tag.E6 K (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
        kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))}) := by
    refine AddSubgroup.closure_induction
      (p := fun x _ => rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ x) ∈
        rootSpan Tag.E6 K (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
          kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})) ?_ ?_ ?_ ?_ hku
    · rintro x ⟨γ, hγ, hγα, hγβ, rfl⟩
      have h3ii' := h3ii K hchar ζ hζ hζo α β γ hα hβ hαβ hγ hγα hγβ
      rw [← ha, ← hb] at h3ii'
      convert h3ii' using 1
      congr 1
    · rw [kgZetaE6_zero, rootDiagUnit_one]
      exact one_mem _
    · intro x y hx hy hpx hpy
      rw [kgZetaE6_add, rootDiagUnit_mul]
      exact mul_mem hpx hpy
    · intro x hx hpx
      rw [kgZetaE6_neg, ← rootDiagUnit_inv]
      exact inv_mem hpx
  have hdu_adj : rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ u))) ∈
      adjointGroup Tag.E6 K := rootSpan_le_adjointGroup K _ hdu
  obtain ⟨r, hr⟩ := show rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ u))) ∈
      (kgThetaHom g).range from by rw [kgThetaHom_range g hg]; exact hdu_adj
  obtain ⟨l, rfl⟩ := hψ r
  refine ⟨l, ?_, ?_⟩
  · show kgThetaHom g (ψ l) ∈ rootSpan Tag.E6 K (kgKernelE6
      {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)), kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})
    rw [hr]
    exact hdu
  · refine mulAut_eq_of_comp_eq ψ hker hperf (fun x => ?_)
    apply kgThetaHom_injective g
    rw [kgThetaHom_conj_apply g ψ l x hr, hconj u x]

end CFSG.StandardType.KGL
end
