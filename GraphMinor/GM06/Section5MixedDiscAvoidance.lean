module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5EnclosingDiscDetour
import GraphMinor.GM06.Section5AttachedDiscDetour

/-!
# Detours around discs with a possible common attachment

For Reduction 2 in VI (5.5), page 130, the region enclosures
include both discs attached at the separation vertex and ordinary
discs inside regions. At an attached boundary use the attachment
visit detour. Otherwise the boundary misses the drawing entirely.
Successive detours preserve earlier avoidance because every new
point lies on a boundary that misses the discarded set.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A finite family whose boundaries meet the drawing only at a
possible common attachment can be avoided without increasing potential. -/
theorem exists_helix_detouring_finite_disc_family_with_attachment
    {k : ℕ} {G : Drawing ClosedCylinder} {s : ClosedCylinder} (hsG : s ∈ G.V)
    {F : Set (Set ClosedCylinder)} (hF : F.Finite)
    (A : Set ClosedCylinder) (hsA : s ∉ A)
    (hdisc : ∀ D ∈ F, IsClosedDisc D)
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
      (fun E hE => hbd E (Or.inr hE)) f hf
    have hex : ∃ u : Curve ClosedCylinder, IsHelix k G u ∧
        Disjoint (range u) (discInt D) ∧ curvePhi k G u ≤ curvePhi k G g ∧
        range u ⊆ range g ∪ discBd D := by
      by_cases hs : s ∈ discBd D
      · exact exists_helix_detour_around_attached_disc g hg (hdisc D (Or.inl rfl)) hs hsG
          (fun x hx => hbd D (Or.inl rfl) ⟨hx.1, Or.inl hx.2⟩)
      · apply exists_helix_avoiding_enclosing_disc_of_boundary_disjoint g hg (hdisc D (Or.inl rfl))
        apply disjoint_left.mpr
        intro x hxb hxG
        have he : x = s := hbd D (Or.inl rfl) ⟨hxb, Or.inl hxG⟩
        exact hs (he ▸ hxb)
    obtain ⟨u, hu, huD, hφu, hur⟩ := hex
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


/-- A finite cover by discs with one possible boundary attachment
gives a helix avoiding the covered discarded set. -/
theorem exists_helix_avoiding_finitely_enclosed_set_with_attachment
    {k : ℕ} {G : Drawing ClosedCylinder} {s : ClosedCylinder} (hsG : s ∈ G.V)
    {F : Set (Set ClosedCylinder)} (hF : F.Finite)
    (A : Set ClosedCylinder) (hsA : s ∉ A)
    (hdisc : ∀ D ∈ F, IsClosedDisc D)
    (hbd : ∀ D ∈ F, discBd D ∩ (G.U ∪ A) ⊆ {s})
    (hcover : A ⊆ ⋃ D ∈ F, discInt D)
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ Disjoint (range g) A ∧
      curvePhi k G g ≤ curvePhi k G f := by
  obtain ⟨g, hg, hφ, hgr⟩ := exists_helix_detouring_finite_disc_family_with_attachment
    hsG hF A hsA hdisc hbd f hf
  exact ⟨g, hg, disjoint_left.mpr (fun x hx hxA => (hgr ⟨hx, hxA⟩).2 (hcover hxA)), hφ⟩

end GraphMinor.GM06
