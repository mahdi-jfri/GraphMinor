module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5EnclosingDiscDetour
import GraphMinor.GM06.Section5AttachedDiscDetour

/-!
# A finite family of discarded-component enclosures

For the Reduction 2 argument of VI (5.5), page 130, apply the
enclosing-disc detour to finitely many discs. Every new point of
a detour lies on its disc boundary. If those boundaries miss the
discarded material, no detour restores a discarded contact removed
by an earlier one. Thus overlapping and nested enclosures are allowed.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Successive enclosing-disc detours remove all discarded contacts
in their interiors and create no discarded contact elsewhere. -/
theorem exists_helix_detouring_finite_disc_family
    {k : ℕ} {G : Drawing ClosedCylinder}
    {F : Set (Set ClosedCylinder)} (hF : F.Finite) (A : Set ClosedCylinder)
    (hdisc : ∀ D ∈ F, IsClosedDisc D)
    (hbd : ∀ D ∈ F, Disjoint (discBd D) (G.U ∪ A))
    (hcuff : ∀ D ∈ F, Disjoint D (bd ClosedCylinder))
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k G f ∧
      range g ∩ A ⊆ (range f ∩ A) \ ⋃ D ∈ F, discInt D := by
  classical
  induction F, hF using Set.Finite.induction_on generalizing f with
  | empty =>
    refine ⟨f, hf, le_rfl, ?_⟩
    simp
  | @insert D F hDF hF ih =>
    obtain ⟨g, hg, hφg, hgr⟩ := ih (fun E hE => hdisc E (Or.inr hE))
      (fun E hE => hbd E (Or.inr hE)) (fun E hE => hcuff E (Or.inr hE)) f hf
    obtain ⟨u, hu, huD, hφu, hur⟩ := exists_helix_avoiding_enclosing_disc g hg
      (hdisc D (Or.inl rfl)) ((hbd D (Or.inl rfl)).mono_right subset_union_left)
      (hcuff D (Or.inl rfl))
    refine ⟨u, hu, hφu.trans hφg, ?_⟩
    rintro x ⟨hxu, hxA⟩
    have hxg : x ∈ range g := (hur hxu).resolve_right (fun hxb =>
      disjoint_left.mp (hbd D (Or.inl rfl)) hxb (Or.inr hxA))
    obtain ⟨hxfA, hxold⟩ := hgr ⟨hxg, hxA⟩
    refine ⟨hxfA, ?_⟩
    rintro hx
    obtain ⟨E, hE, hxE⟩ := mem_iUnion₂.mp hx
    rcases hE with rfl | hE
    · exact disjoint_left.mp huD hxu hxE
    · exact hxold (mem_iUnion₂.mpr ⟨E, hE, hxE⟩)

/-- A finite disc cover of discarded material, with boundaries off
both drawings and discs off the cuffs, gives an avoiding helix. -/
theorem exists_helix_avoiding_finitely_enclosed_set
    {k : ℕ} {G : Drawing ClosedCylinder}
    {F : Set (Set ClosedCylinder)} (hF : F.Finite) (A : Set ClosedCylinder)
    (hdisc : ∀ D ∈ F, IsClosedDisc D)
    (hbd : ∀ D ∈ F, Disjoint (discBd D) (G.U ∪ A))
    (hcuff : ∀ D ∈ F, Disjoint D (bd ClosedCylinder))
    (hcover : A ⊆ ⋃ D ∈ F, discInt D)
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ Disjoint (range g) A ∧
      curvePhi k G g ≤ curvePhi k G f := by
  obtain ⟨g, hg, hφ, hgr⟩ := exists_helix_detouring_finite_disc_family
    hF A hdisc hbd hcuff f hf
  exact ⟨g, hg, disjoint_left.mpr (fun x hx hxA => (hgr ⟨hx, hxA⟩).2 (hcover hxA)), hφ⟩

/-- Successive disc detours at one attachment remove all enclosed
contacts away from that attachment, including for helices visiting it. -/
theorem exists_helix_detouring_finite_attached_disc_family
    {k : ℕ} {G : Drawing ClosedCylinder} {s : ClosedCylinder} (hsG : s ∈ G.V)
    {F : Set (Set ClosedCylinder)} (hF : F.Finite)
    (A : Set ClosedCylinder) (hsA : s ∉ A)
    (hdisc : ∀ D ∈ F, IsClosedDisc D)
    (hsbd : ∀ D ∈ F, s ∈ discBd D)
    (hbd : ∀ D ∈ F, discBd D ∩ (G.U ∪ A) ⊆ {s})
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k G f ∧
      range g ∩ A ⊆ (range f ∩ A) \ ⋃ D ∈ F, discInt D := by
  classical
  induction F, hF using Set.Finite.induction_on generalizing f with
  | empty =>
    refine ⟨f, hf, le_rfl, ?_⟩
    simp
  | @insert D F hDF hF ih =>
    obtain ⟨g, hg, hφg, hgr⟩ := ih (fun E hE => hdisc E (Or.inr hE))
      (fun E hE => hsbd E (Or.inr hE)) (fun E hE => hbd E (Or.inr hE)) f hf
    obtain ⟨u, hu, huD, hφu, hur⟩ := exists_helix_detour_around_attached_disc g hg
      (hdisc D (Or.inl rfl)) (hsbd D (Or.inl rfl)) hsG
      (fun x hx => hbd D (Or.inl rfl) ⟨hx.1, Or.inl hx.2⟩)
    refine ⟨u, hu, hφu.trans hφg, ?_⟩
    rintro x ⟨hxu, hxA⟩
    have hxg : x ∈ range g := (hur hxu).resolve_right (fun hxb => by
      have he : x = s := hbd D (Or.inl rfl) ⟨hxb, Or.inr hxA⟩
      exact hsA (he ▸ hxA))
    obtain ⟨hxfA, hxold⟩ := hgr ⟨hxg, hxA⟩
    refine ⟨hxfA, ?_⟩
    rintro hx
    obtain ⟨E, hE, hxE⟩ := mem_iUnion₂.mp hx
    rcases hE with rfl | hE
    · exact disjoint_left.mp huD hxu hxE
    · exact hxold (mem_iUnion₂.mpr ⟨E, hE, hxE⟩)

/-- A finite family of attached enclosures gives an avoiding helix
without adding any visit away from its common attachment. -/
theorem exists_helix_avoiding_finitely_attached_enclosed_set
    {k : ℕ} {G : Drawing ClosedCylinder} {s : ClosedCylinder} (hsG : s ∈ G.V)
    {F : Set (Set ClosedCylinder)} (hF : F.Finite)
    (A : Set ClosedCylinder) (hsA : s ∉ A)
    (hdisc : ∀ D ∈ F, IsClosedDisc D)
    (hsbd : ∀ D ∈ F, s ∈ discBd D)
    (hbd : ∀ D ∈ F, discBd D ∩ (G.U ∪ A) ⊆ {s})
    (hcover : A ⊆ ⋃ D ∈ F, discInt D)
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ Disjoint (range g) A ∧
      curvePhi k G g ≤ curvePhi k G f := by
  obtain ⟨g, hg, hφ, hgr⟩ := exists_helix_detouring_finite_attached_disc_family
    hsG hF A hsA hdisc hsbd hbd f hf
  exact ⟨g, hg, disjoint_left.mpr (fun x hx hxA => (hgr ⟨hx, hxA⟩).2 (hcover hxA)), hφ⟩

end GraphMinor.GM06
