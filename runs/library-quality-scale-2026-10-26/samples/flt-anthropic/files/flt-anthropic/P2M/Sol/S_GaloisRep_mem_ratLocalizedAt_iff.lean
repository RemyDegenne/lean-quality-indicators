import Definitions.Def_GaloisRep_Flat
import P2M.Util
namespace P2MW.S_GaloisRep_mem_ratLocalizedAt_iff

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt"
namespace FlatSol
p2m_open "GaloisRep"

theorem mem_ratLocalizedAt_iff_coprime {p : ℕ} (q : ℚ) :
    q ∈ ratLocalizedAt p ↔ q.den.Coprime p :=
  Iff.rfl

theorem mem_ratLocalizedAt_iff {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ ratLocalizedAt p ↔ ¬ p ∣ q.den := by
  rw [mem_ratLocalizedAt_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd]

end GaloisRep.FlatSol

theorem solution
    {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ¬ p ∣ q.den :=
  GaloisRep.FlatSol.mem_ratLocalizedAt_iff hp q
