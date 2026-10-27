public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64

open LinearMap (BilinForm)

open scoped Pointwise

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))

local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)

local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))

local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)

theorem ptLinFun_eq (halt : AltOrbit z φ e) {m : 𝒩₁} {s : bilinIsometryGroup (b.restrict 𝔼)}
    (hs : ∀ w, ptAct hzC hsup hinf hz hb hnd hV φ he halt m w =
      OddQuadraticFive.sE s w + ptAct hzC hsup hinf hz hb hnd hV φ he halt m 0) :
    ptLinFun hzC hsup hinf hz hb hnd hV φ he halt m = s := by
  refine Subtype.ext (Units.ext (LinearMap.ext fun w => ?_))
  have h := (ptLinFun_spec hzC hsup hinf hz hb hnd hV φ he halt m w).symm.trans (hs w)
  exact add_right_cancel h

end Setting
end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
end
