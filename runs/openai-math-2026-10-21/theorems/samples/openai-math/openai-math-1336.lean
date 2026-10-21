namespace OAI

set_option autoImplicit true

section

namespace ExactDerandomization.SiteX.Line.Fabric

open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Plaza _root_.OAI.ExactDerandomization.Sub

open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme

open Dome Cone ConeX Buf At MintV Line Line.Fabric Producer Label

noncomputable section

open scoped Classical

variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}

variable (v:Fabric u)(p:Producer)(κ:ℕ)

variable {v p κ}

namespace Bloom12

variable {l:ℕ→List Swirl.Gem}(h0:Bloom12 v p κ l)

include h0

lemma funded (hS:u.v.A*(2*u.v.A+40)  ≤  u.v.slope)
    (_:v.Mantle κ)
    (hf:∀ i z b,i<v.Rslots→ 1 ≤ z→z  ≤ clim u.w0.p→∀ a y,
        Lot.Mane u.D.l u.v.slope ⟨u.D.W v.core12,0⟩ 1 (bell v.core12 (idx b i z) 0) (fullB u.r u.v u.s.pave) a y →
        Lot.Mane u.D.l u.v.slope ⟨u.D.W v.core12,0⟩ 1 (bell v.core12 (idx b i z) 0) u.D.l.P a y)
    (i:ℕ): u.D.Streams (v.slotWord i) ((v.alongE p κ).valueOf l (clim u.w0.p) i) := by
   let e:=v.alongE p κ; have hh:u.D.Suite v.core12:=h0.quilt.h.supply
   let k:=clim u.w0.p
   refine ⟨fun z hz x hx b r hr=>?_,fun z hz x hx b r hg=>?_,fun x hx z hz y hy r m he hp=>?_⟩
   · have he:u.D.pulseQ (v.slotWord i) z b=bell v.core12 (idx b i z) 0:=v.adding ..
     have hp:= (cap_dual hh).1 hz
     have hC := h0.mouth.clearsWay k i hp.1 z b hx hr
     let c:= e.valueOf l k i z b x
     have hi:Lot.Mane u.D.l (Ember.stepC e.A) ⟨u.D.W v.core12,0⟩ 1 (bell v.core12 (idx b i z) 0)
                 (renbody (Ember.cutWay e.p e.R e.D.s e.A k i z b)) (0,glove r x) (Dome.AtM c r x):=
             reprise hC (by simp [substitute]; rfl)
     have hj:i<v.Rslots:=hp.1; have hz1:z ≤  clim u.w0.p:= hp.2.2
     have hk: Lot.Mane u.D.l (Ember.stepC e.A) ⟨u.D.W v.core12,0⟩ 1 (bell v.core12 (idx b i z) 0)
                           (fullB u.r u.v u.s.pave) (0,glove r x) (Dome.AtM c r x):= by
        refine pickout u.r u.v u.s.pave _ ?_ b hi
        simpa only [Finset.mem_toList,neighbors,mem_product,mem_range] using (show i < v.Rslots ∧ z<clim u.w0.p+1 from ⟨hp.1,by omega⟩)
     have hn : 1 ≤  Ember.stepC e.A:=by
          have hs:=h0.quilt.h.skeleton; have hz:=h0.quilt.h.budget
          change _  ≤  e.A at hz; unfold Ember.stepC; change _ ≤ e.k at hs; nlinarith
     have hG := hf i z b hp.1 hp.2.1 hp.2.2 _ _ (hk.mono hS hn)
     have ht:= Night.pairbill u.r u.v u.x u.prog (v.slotWord i) z hz b
     have hg:u.D.pulseQ (v.slotWord i) z b  ≤  u.D.F.limit:=ht
     rw [he] at hg ⊢
     have hp0:u.D.D v.core12=1:=v.ageEnd _ (by decide)
     rw [← hp0] at hG
     exact hh.hired _ 0 hg (by have :=hh.shape.price; change 1 ≤ u.v.slope; change 2 ≤ u.v.slope at this; omega)
                   (by change u.v.slope ≤ u.v.slope; exact le_rfl) hG
   · have he:=h0.mouth.disp.1 hg
     exact ⟨(h0.mouth.pointIn he).1,h0.mouth.disp.2 ((Ember.Mouth.exchange0 b).1 he)⟩
   exact (h0.mouth.unique0 he hp).symm

end Bloom12
end
end ExactDerandomization.SiteX.Line.Fabric
end
end OAI
