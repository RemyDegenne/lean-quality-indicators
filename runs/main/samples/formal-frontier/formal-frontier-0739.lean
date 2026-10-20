@[expose] public section

universe u

namespace ProfiniteGrp

@[simp] theorem powerImage_quotientMap_zmod (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    {d n : ℕ} (hdn : d ∣ n) (hn : 0 < n)
    (hindex : (powerImage G hG n : Subgroup G).index = n)
    (a : ZMod n) :
    powerImage_quotientMap G hG hdn
        (powerImage_zmodContinuousMulEquiv G hG g hg n hn hindex
          (Multiplicative.ofAdd a)) =
      powerImage_zmodContinuousMulEquiv G hG g hg d
        (Nat.pos_of_dvd_of_pos hdn hn)
        (powerImage_index_eq_of_dvd G hG hdn hn hindex)
        (Multiplicative.ofAdd (ZMod.castHom hdn (ZMod d) a)) := by
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
  have hsource : Multiplicative.ofAdd (k : ZMod n) =
      (Multiplicative.ofAdd (1 : ZMod n)) ^ k := by
    simp only [← ofAdd_nsmul, nsmul_one]
  have htarget : Multiplicative.ofAdd (k : ZMod d) =
      (Multiplicative.ofAdd (1 : ZMod d)) ^ k := by
    simp only [← ofAdd_nsmul, nsmul_one]
  rw [hsource, map_pow, powerImage_zmodContinuousMulEquiv_apply_one,
    map_pow, powerImage_quotientMap_apply_mk, map_natCast, htarget,
    map_pow, powerImage_zmodContinuousMulEquiv_apply_one]

end ProfiniteGrp
end
