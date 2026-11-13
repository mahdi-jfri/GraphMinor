module

public import GraphMinor.GM08.Section15Defs
public import GraphMinor.GM12.Section3Punctured
import GraphMinor.GM08.Section17FreeHole
import GraphMinor.GM08.Section15PuncturedCylinder
import GraphMinor.GM08.Section15PuncturedDrawing
import GraphMinor.GM07.Section9DiscSphere
import GraphMinor.GM07.CylinderCap

/-!
# Reading a sphere drawing in a cylinder with a free joining arc

Keep an empty disc on one side of the drawing, and choose a free hole
next to a free point on its boundary. Removing the two interiors gives
a cylinder. The drawing and graph stay the same, its boundary vertices
are exactly those on the retained disc boundary, and the arc between
the two boundaries misses the drawing. This is the change of ambient
surface for the empty-cuff part of VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- Removing a free hole next to an empty disc gives a cylinder drawing
with a free cuff-joining arc and the same boundary roots on the retained
disc. This is used in VIII (17.2), page 284. -/
theorem exists_free_cylinder_drawing {S : Type w} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) (hsph : IsSphere S)
    (G : Drawing S) {D : Set S} (hD : IsClosedDisc D)
    (hoff : Disjoint (discInt D) G.U) (hn : G.IsNormal (discBd D))
    {p : S} (hp : p ∈ discBd D) (hpoff : p ∉ G.U) :
    ∃ E : Set S, IsClosedDisc E ∧ Disjoint D E ∧
      let Q := GM12.discComplement (![D, E] : Fin 2 → Set S)
      ∃ H : Drawing Q, IsCylinder Q ∧ H.IsProper ∧
        (Subtype.val : Q → S) '' (H.V ∩ bd Q) = G.V ∩ discBd D ∧
        (∃ i : Iso H.toGraph G.toGraph,
          ∀ v : H.V, (i.vertexEquiv v).1 = v.1.1) ∧
        ∃ (C₁ C₂ I : Set Q) (a b : Q),
          C₁ ∈ cuffs Q ∧ C₂ ∈ cuffs Q ∧ C₁ ≠ C₂ ∧
          IsLineWithEnds I a b ∧ a ∈ C₁ ∧ b ∈ C₂ ∧ Disjoint I H.U := by
  have : T2Space S := hS.2.1
  obtain ⟨E, J, a, b, hE, hDE, hEG, hJ, ha, hb, hends, hJG⟩ :=
    exists_free_disc_and_joining_line hS G hD hp hpoff
  have hnE : G.IsNormal (discBd E) := fun x hx =>
    False.elim (disjoint_left.mp hEG (discBd_subset E hx.1) hx.2)
  obtain ⟨H, hHU, _, hHproper, hroots, hi⟩ :=
    exists_drawing_in_two_disc_complement hS G hD hE hDE hoff
      (hEG.mono_left (discInt_subset E)) hn hnE
  obtain ⟨hQ, hcuffs, hne, _⟩ := cylinder_complement_two_discs hS hsph hD hE hDE
  let P : Fin 2 → Set S := ![D, E]
  let Q := GM12.discComplement P
  have hP : ∀ i, IsClosedDisc (P i) := by intro i; fin_cases i <;> assumption
  have hdis : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hDE
    · exact hDE.symm
    · exact (hij rfl).elim
  have hJQ : J ⊆ GM12.discComplement P := by
    intro x hxJ
    apply (GM07.mem_discComplement_iff hS P hP hdis x).mpr
    intro i hxint
    have hxDE : x ∈ D ∪ E := by
      fin_cases i
      · exact .inl hxint.1
      · exact .inr hxint.1
    have hxend : x ∈ ({a, b} : Set S) := hends ▸ ⟨hxJ, hxDE⟩
    rcases hxend with rfl | rfl
    · fin_cases i
      · exact hxint.2 ha
      · exact disjoint_left.mp hDE (discBd_subset D ha) hxint.1
    · fin_cases i
      · exact disjoint_left.mp hDE hxint.1 (discBd_subset E hb)
      · exact hxint.2 hb
  let aQ : Q := ⟨a, hJQ hJ.left_mem⟩
  let bQ : Q := ⟨b, hJQ hJ.right_mem⟩
  let incl : Q → S := Subtype.val
  have hline : IsLineWithEnds (incl ⁻¹' J) aQ bQ :=
    GM07.pull_line IsEmbedding.subtypeVal hJ (fun x hx => ⟨⟨x, hJQ hx⟩, rfl⟩)
  have hrootD : (Subtype.val : Q → S) '' (H.V ∩ bd Q) = G.V ∩ discBd D := by
    rw [hroots]
    apply subset_antisymm
    · rintro x ⟨hxV, hxD | hxE⟩
      · exact ⟨hxV, hxD⟩
      · exact False.elim (disjoint_left.mp hEG (discBd_subset E hxE) (G.V_subset_U hxV))
    · exact fun x hx => ⟨hx.1, .inl hx.2⟩
  refine ⟨E, hE, hDE, H, hQ, hHproper, hrootD, hi,
    incl ⁻¹' discBd D, incl ⁻¹' discBd E, incl ⁻¹' J, aQ, bQ,
    ?_, ?_, hne, hline, ha, hb, ?_⟩
  · rw [hcuffs]
    exact .inl rfl
  · rw [hcuffs]
    exact .inr rfl
  · apply disjoint_left.mpr
    intro x hxJ hxH
    have hxG : incl x ∈ G.U := by
      change x ∈ incl ⁻¹' G.U
      exact hHU ▸ hxH
    exact disjoint_left.mp hJG hxJ hxG

end GraphMinor.GM08
