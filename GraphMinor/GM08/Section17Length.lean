module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15Menger

/-!
# The arc condition for the cylinder minor theorem

In the application of VII (9.3) to VIII (17.2), an arc need only meet
both hoops. Restrict its interval parameter to two such points. The
tube length bounds the vertex count of this subarc, hence also that
of the original arc.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- The tube length bounds every normal line meeting both boundary
hoops. This supplies condition (ii) of VII (9.3) in VIII (17.2),
page 284. -/
theorem Tube.length_le_ncard_of_line_meeting_hoops {S : Type w}
    [TopologicalSpace S] (τ : Tube S) {I : Set S}
    (hI : IsLine I) (hN : τ.Γ.IsNormal I)
    (h₁ : (I ∩ τ.F₁).Nonempty) (h₂ : (I ∩ τ.F₂).Nonempty)
    (hdis : Disjoint τ.F₁ τ.F₂) :
    τ.length ≤ (τ.Γ.V ∩ I).ncard := by
  have : T2Space S := τ.t2Space
  obtain ⟨e⟩ := hI
  obtain ⟨a, haI, ha⟩ := h₁
  obtain ⟨b, hbI, hb⟩ := h₂
  let f : unitInterval → S := fun t => (e t).1
  let s := e.symm ⟨a, haI⟩
  let t := e.symm ⟨b, hbI⟩
  have hfs : f s = a := congrArg Subtype.val (e.apply_symm_apply ⟨a, haI⟩)
  have hft : f t = b := congrArg Subtype.val (e.apply_symm_apply ⟨b, hbI⟩)
  have hne : s ≠ t := by
    intro h
    have hab : a = b := hfs.symm.trans ((congrArg f h).trans hft)
    exact disjoint_left.mp hdis ha (hab.symm ▸ hb)
  have hfc : Continuous f := continuous_subtype_val.comp e.continuous
  have hfi : Function.Injective f := Subtype.val_injective.comp e.injective
  have hsub : ∀ A : Set unitInterval, f '' A ⊆ I := by
    rintro A x ⟨r, _, rfl⟩
    exact (e r).2
  have hbound : ∀ {J : Set S}, J ⊆ I →
      IsLineWithEnds J a b → τ.length ≤ (τ.Γ.V ∩ I).ncard := by
    intro J hJI hJ
    have hJN : τ.Γ.IsNormal J := fun x hx => hN ⟨hJI hx.1, hx.2⟩
    exact ((τ.le_length_iff).mp le_rfl J a b hJ ha hb hJN).trans
      (ncard_le_ncard (fun x hx => ⟨hx.2, hJI hx.1⟩)
        (τ.Γ.finite_V.inter_of_left I))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply hbound (hsub (Icc s t))
    simpa only [hfs, hft] using subArc_of_lt hfc hfi hlt
  · apply hbound (hsub (Icc t s))
    have h := (subArc_of_lt hfc hfi hgt).symm
    simpa only [hfs, hft] using h

/-- A subtube length bounds the full drawing's count on every normal
line meeting both inner hoops, as required in VIII (17.2). -/
theorem Tube.subTube_length_le_ncard_of_line {S : Type w}
    [TopologicalSpace S] (τ : Tube S) {A B I : Set S}
    (hlam : AreLaminarHoops A B) (hNA : τ.Γ.IsNormal A) (hNB : τ.Γ.IsNormal B)
    (hI : IsLine I) (hN : τ.Γ.IsNormal I)
    (hA : (I ∩ A).Nonempty) (hB : (I ∩ B).Nonempty)
    (hdis : Disjoint A B) :
    (τ.subTube hlam hNA hNB).length ≤ (τ.Γ.V ∩ I).ncard := by
  have : T2Space S := τ.t2Space
  let σ := τ.subTube hlam hNA hNB
  have hcl := isClosed_cylinderBetween hlam
  have hU : σ.Γ.U ⊆ τ.Γ.U ∩ cylinderBetween A B :=
    interSet_U_subset_of_isClosed τ.Γ hcl
  have hV : σ.Γ.V = τ.Γ.V ∩ cylinderBetween A B :=
    interSet_V_of_isClosed τ.Γ hcl
  have hNI : σ.Γ.IsNormal I := by
    intro x hx
    rw [hV]
    exact ⟨hN ⟨hx.1, (hU hx.2).1⟩, (hU hx.2).2⟩
  exact (σ.length_le_ncard_of_line_meeting_hoops hI hNI hA hB hdis).trans
    (ncard_le_ncard (fun x hx => ⟨(hV.subset hx.1).1, hx.2⟩)
      (τ.Γ.finite_V.inter_of_left I))

end GraphMinor.GM08
