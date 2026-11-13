module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.CutLift
import GraphMinor.Surface.EdgeLoop
import GraphMinor.Surface.ChartCells
import GraphMinor.Surface.DiscFan
import GraphMinor.Surface.ArcTools
import GraphMinor.GM11.Fan
import GraphMinor.GM11.OArcCircuit

/-!
# Three lines in a circle

A circle has only two directions at each of its points. So three lines in a
circle cannot leave one point `q` in three different directions. We use this
to follow the sides of the pinched cut (`exists_pinched_cut`): two lifts of a
line that end at the same point would leave that point in the same direction
as a third lift.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

variable {X : Type w} [TopologicalSpace X] [T2Space X]

/-- **Three lines in a circle.** Let `P`, `Q`, `R` be lines in a circle `J`
that start at one point `q`. Suppose `R` meets `P` and `Q` only at `q`, and
`P` meets `Q` only at `q` and maybe at a common far end. This is impossible. -/
theorem false_of_three_lines {J P Q R : Set X} {q a b c : X} (hJ : IsOArc J)
    (hP : IsLineWithEnds P q a) (hQ : IsLineWithEnds Q q b) (hR : IsLineWithEnds R q c)
    (hPJ : P ⊆ J) (hQJ : Q ⊆ J) (hRJ : R ⊆ J)
    (hPQ : ∀ x ∈ P, x ∈ Q → x = q ∨ (x = a ∧ x = b))
    (hPR : ∀ x ∈ P, x ∈ R → x = q) (hQR : ∀ x ∈ Q, x ∈ R → x = q) : False := by
  have hqa : q ≠ a := hP.ne'
  have hqb : q ≠ b := hQ.ne'
  have hqc : q ≠ c := hR.ne'
  -- every point of `R` other than `q` is off `P ∪ Q`
  have hRoff : ∀ x ∈ R, x ≠ q → x ∉ P ∪ Q := by
    rintro x hxR hxq (hxP | hxQ)
    · exact hxq (hPR x hxP hxR)
    · exact hxq (hQR x hxQ hxR)
  by_cases hab : a = b
  · -- `P ∪ Q` is a circle, so it is all of `J`, and it holds `c`
    subst hab
    have hi : P ∩ Q = {q, a} := by
      ext x
      refine ⟨fun hx => ?_, ?_⟩
      · rcases hPQ x hx.1 hx.2 with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      · rintro (rfl | rfl)
        · exact ⟨hP.left_mem, hQ.left_mem⟩
        · exact ⟨hP.right_mem, hQ.right_mem⟩
    have hO : IsOArc (P ∪ Q) := oArc_of_lines hP hQ hi
    have heq : P ∪ Q = J := GM11.eq_of_oArc_subset hO hJ (union_subset hPJ hQJ)
    exact hRoff c hR.right_mem hqc.symm (heq ▸ hRJ hR.right_mem)
  · -- `P ∪ Q` is a line from `a` to `b` through `q`
    have hi : P ∩ Q = {q} := by
      ext x
      refine ⟨fun hx => ?_, ?_⟩
      · rcases hPQ x hx.1 hx.2 with h | h
        · exact h
        · exact absurd (h.1.symm.trans h.2) hab
      · rintro rfl
        exact ⟨hP.left_mem, hQ.left_mem⟩
    have hL : IsLineWithEnds (P ∪ Q) a b := hP.symm.union hQ hi
    have hLpc : IsPreconnected (P ∪ Q) := by
      obtain ⟨f, -, -⟩ := hL
      have : ConnectedSpace (P ∪ Q : Set X) := f.surjective.connectedSpace f.continuous
      exact isPreconnected_iff_preconnectedSpace.mpr inferInstance
    have haJ : a ∈ J := hPJ hP.right_mem
    have hbJ : b ∈ J := hQJ hQ.right_mem
    obtain ⟨L₁, L₂, hL₁, hL₂, hun, hint⟩ := hJ.lines haJ hbJ hab
    have hL₁c : IsClosed L₁ := hL₁.isCompact.isClosed
    have hL₂c : IsClosed L₂ := hL₂.isCompact.isClosed
    -- the inside of `P ∪ Q` lies in one of the two arcs of `J`
    have hsub : (P ∪ Q) \ {a, b} ⊆ L₁ ∪ L₂ := fun x hx =>
      hun ▸ union_subset hPJ hQJ hx.1
    have hmiss : (P ∪ Q) \ {a, b} ∩ (L₁ ∩ L₂) = ∅ := by
      rw [hint, eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hx'⟩
      exact hx.2 hx'
    -- in the arc `L` that holds `P ∪ Q`, `q` is not an end, so `R` must leave `L`
    have key : ∀ {L L' : Set X}, IsLineWithEnds L a b → IsClosed L' → L ∩ L' = {a, b} →
        L ∪ L' = J → (P ∪ Q) \ {a, b} ⊆ L → False := by
      intro L L' hLl hL'c hLL' hLJ hin
      have hPQL : P ∪ Q ⊆ L := by
        intro x hx
        by_cases hxab : x ∈ ({a, b} : Set X)
        · rcases hxab with rfl | rfl
          · exact hLl.left_mem
          · exact hLl.right_mem
        · exact hin ⟨hx, hxab⟩
      have heq : P ∪ Q = L :=
        hLl.eq_of_subset hLpc hPQL (Or.inl hP.right_mem) (Or.inr hQ.right_mem)
      have hRL' : R \ {q} ⊆ L' := by
        intro x hx
        have hxJ : x ∈ L ∪ L' := hLJ ▸ hRJ hx.1
        rcases hxJ with hxL | hxL'
        · exact absurd (heq ▸ hxL) (hRoff x hx.1 hx.2)
        · exact hxL'
      have hqL' : q ∈ L' :=
        closure_minimal hRL' hL'c (GM11.IsLineWithEnds.mem_closure_sdiff hR)
      have hqL : q ∈ L := heq ▸ Or.inl hP.left_mem
      have hq : q ∈ L ∩ L' := ⟨hqL, hqL'⟩
      rw [hLL'] at hq
      rcases hq with h | h
      · exact hqa h
      · exact hqb h
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hL.isPreconnected_diff) L₁ L₂
        hL₁c hL₂c hsub hmiss with h | h
    · exact key hL₁ hL₂c hint hun h
    · exact key hL₂ hL₁c (by rw [inter_comm, hint]) (by rw [union_comm, hun]) h

end GraphMinor.GM08

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- A compact set that a map sends one to one onto a line is a line, with the
lifted ends. -/
theorem isLineWithEnds_of_bijOn {T S : Type w} [TopologicalSpace T] [TopologicalSpace S]
    [T2Space S] {ψ : T → S} (hψ : Continuous ψ) {X : Set T} (hX : IsCompact X) {L : Set S}
    {u v : S} (hL : IsLineWithEnds L u v) (hb : BijOn ψ X L) :
    ∃ x ∈ X, ∃ y ∈ X, ψ x = u ∧ ψ y = v ∧ IsLineWithEnds X x y := by
  have : CompactSpace X := isCompact_iff_compactSpace.mp hX
  have : T2Space L := inferInstance
  let g : X → L := fun w => ⟨ψ w, hb.mapsTo w.2⟩
  have hg : Continuous g := (hψ.comp continuous_subtype_val).subtype_mk _
  have hgb : Function.Bijective g := by
    refine ⟨fun a b h => Subtype.ext (hb.injOn a.2 b.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := hb.surjOn hz
    exact ⟨⟨w, hw⟩, rfl⟩
  let e : X ≃ₜ L := hg.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb)
  obtain ⟨f, h0, h1⟩ := hL
  refine ⟨(e.symm (f 0)).1, (e.symm (f 0)).2, (e.symm (f 1)).1, (e.symm (f 1)).2, ?_, ?_,
    ⟨f.trans e.symm, rfl, rfl⟩⟩
  · have : g (e.symm (f 0)) = f 0 := e.apply_symm_apply (f 0)
    rw [← h0]
    exact congrArg Subtype.val this
  · have : g (e.symm (f 1)) = f 1 := e.apply_symm_apply (f 1)
    rw [← h1]
    exact congrArg Subtype.val this

/-- A line is connected. -/
theorem line_isPreconnected {T : Type w} [TopologicalSpace T] {L : Set T} {u v : T}
    (h : IsLineWithEnds L u v) : IsPreconnected L := by
  obtain ⟨f, -, -⟩ := h
  have : ConnectedSpace L := f.surjective.connectedSpace f.continuous
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

/-- A line is compact. -/
theorem isLine_isCompact {T : Type w} [TopologicalSpace T] {L : Set T} (h : IsLine L) :
    IsCompact L := by
  obtain ⟨f⟩ := h
  have : CompactSpace L := f.compactSpace
  exact isCompact_iff_compactSpace.mpr this

end GraphMinor.GM08
