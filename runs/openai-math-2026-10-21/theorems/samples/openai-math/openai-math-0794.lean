namespace OAI

namespace PolynomialVacuumCylinder

open Classical

variable {M H : ℕ} [NeZero M]

namespace BoundaryArc

theorem start_port (A : BoundaryArc (bandSites M H)) :
    A.start=(if A.port.1 then (.down A.port.2 ((H : ℤ)-1),0) else (.up A.port.2 0,0)) := by
  have hb:=band_boundary H A.start.1 A.start.2 ((mem_bandSites H _).mp A.startInside)
    (by simpa only [reverseGerm,mem_bandSites] using A.startOutside)
  rcases hb with ⟨i,hv,hk⟩ | ⟨i,hv,hk⟩
  · have he : A.start=(.up i 0,0) := Prod.ext hv hk
    simp [port,he]
  · have he : A.start=(.down i ((H : ℤ)-1),0) := Prod.ext hv hk
    simp [port,he]

end BoundaryArc
end PolynomialVacuumCylinder
end OAI
