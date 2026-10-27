@[expose] public section

open Set Function

set_option linter.style.haveILetI false

universe u

namespace ProfiniteGrp

/-- The surjective continuous power map, now regarded as taking values in its
actual closed (and hence profinite) range. -/
def powerHomToImage (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (n : ℕ) :
    G →ₜ* ofClosedSubgroup (powerImage G hG n) :=
  ⟨{
    toFun := fun x => ⟨x ^ n, (mem_powerImage_iff G hG n _).mpr ⟨x, rfl⟩⟩
    map_one' := by apply Subtype.ext; change (1 : G) ^ n = 1; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      exact (powerHom G hG n).map_mul x y
  }, (powerHom G hG n).continuous_toFun.subtype_mk
    (fun x => (mem_powerImage_iff G hG n _).mpr ⟨x, rfl⟩)⟩

end ProfiniteGrp
end
