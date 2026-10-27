public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)

include c

section GoodPath

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem top_le_vsix (hZV : c.HZV) (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ}
    (ha : Even a) (h10 : 10 ≤ a) (haN : a + 14 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i) :
    (conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) ⊔
        (conjCl (stab (puAmalgam c.hyp.le) (p a))
            (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) ≤
      conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a)) := by
  have h := c.hyp
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) le_rfl
  have e : whv h (p (a + 2)) (p (a + 2 + 2)) = whv h (p (a + 2)) (p (a + 2 - 2)) :=
    c.whv_eq_of_isGoodPath hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
  rw [show a + 2 + 2 = a + 4 by omega, show a + 2 - 2 = a by omega] at e
  have hγγ : Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)) ≤ whv h (p (a + 2)) (p a) := by
    have := c.vhat_le_whv' hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega] at this
    rwa [← e]
  have hμγ : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ whv h (p (a + 2)) (p a) := by
    rw [← e]; exact c.vhat_le_whv_self
  have hμ'γ : Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4)) ≤ whv h (p (a + 2)) (p a) := by
    have e' : whv h (p' (a + 2)) (p' (a + 2 + 2)) = whv h (p' (a + 2)) (p' (a + 2 - 2)) :=
      c.whv_eq_of_isGoodPath hp' (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega, show a + 2 - 2 = a by omega, hpa, hpa2] at e'
    rw [← e']; exact c.vhat_le_whv_self
  have hWhγ : whv h (p a) (p (a + 2)) ≤
      conjCl (stab (puAmalgam h.le) (p a)) (whv h (p (a + 2)) (p a)) := conjCl_mono hγγ
  exact sup_le (sup_le (conjCl_mono hμγ) hWhγ) (sup_le (conjCl_mono hμ'γ) hWhγ)

end GoodPath
end Ctx
end CFSG.Quasithin.MS93.S45
end
