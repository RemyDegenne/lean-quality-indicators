namespace OAI

namespace TuringRigidity.SentenceCoding

open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel

open BoundedDefinability SetModelFunctions SetModelReals

universe u

variable {M : ZFSet.{u}}

theorem setSupportRecursion_spec (root : SentenceForm) (G : ZFSet.{u}) :
    SetSupportRecursion (family root) G ↔ SupportRecursion root G := by
  constructor
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨c,hc,b,hb,rfl⟩ := hn z hz
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,rfl⟩ := (mem_omega b).mp hb
      exact ⟨p,hp,n,rfl⟩
    · intro p hp n
      exact (hr _ ((code_mem_family root p).mpr hp) _ ((mem_omega _).mpr ⟨n,rfl⟩)).trans
        (setSupportStep_encode G p n)
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨p,hp,n,rfl⟩ := hn z hz
      exact ⟨_,(code_mem_family root p).mpr hp,_,(mem_omega _).mpr ⟨n,rfl⟩,rfl⟩
    · intro c hc b hb
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,rfl⟩ := (mem_omega b).mp hb
      exact (hr p hp n).trans (setSupportStep_encode G p n).symm

end TuringRigidity.SentenceCoding
end OAI
