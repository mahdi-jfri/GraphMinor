module

public import GraphMinor.GM06.Defs
import GraphMinor.GM07.Section11a
import GraphMinor.GM07.Section3
import GraphMinor.GM07.Section11c
import GraphMinor.Surface.CrossCut

/-!
# The disc between two homotopic arcs

In Graph Minors VI, Section 4, page 124, a path homotopic to a cuff arc
encloses a disc with that arc. Two injective arcs meeting only at their ends
form a circle. A homotopy between the arcs contracts this circle onto one arc,
which then contracts to an end. The null-homotopic circle bounds a disc.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

universe u

private theorem exists_arc_inverse {S : Type u} [TopologicalSpace S] [T2Space S]
    (f : Curve S) (hf : f.IsLine) :
    ∃ r : S → unitInterval, ContinuousOn r (range f) ∧ ∀ t, r (f t) = t := by
  classical
  let e : unitInterval ≃ₜ range f :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofInjective f hf) f.continuous.rangeFactorization
  let r : S → unitInterval := fun x => if h : x ∈ range f then e.symm ⟨x, h⟩ else 0
  refine ⟨r, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : (range f).domRestrict r = e.symm := by
      funext x
      change r x.1 = e.symm x
      simp only [r, x.property, ↓reduceDIte]
    rw [heq]
    exact e.symm.continuous
  · intro t
    simp only [r, mem_range_self, ↓reduceDIte]
    exact e.symm_apply_apply t

/-- Two injective arcs with the same ends and no other common points have a
continuous common parameter on their union. This parameter is used to contract
the boundary circle in the proof of Graph Minors VI (4.1), page 124. -/
theorem exists_common_arc_parameter {S : Type u} [TopologicalSpace S] [T2Space S]
    (f g : Curve S) (hf : f.IsLine) (hg : g.IsLine)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hinter : range f ∩ range g ⊆ {f 0, f 1}) :
    ∃ τ : C((range f ∪ range g : Set S), unitInterval),
      (∀ t, τ ⟨f t, Or.inl (mem_range_self t)⟩ = t) ∧
      (∀ t, τ ⟨g t, Or.inr (mem_range_self t)⟩ = t) := by
  classical
  obtain ⟨r, hr, hrf⟩ := exists_arc_inverse f hf
  obtain ⟨q, hq, hqg⟩ := exists_arc_inverse g hg
  let U := range f ∪ range g
  let A : Set U := Subtype.val ⁻¹' range f
  let B : Set U := Subtype.val ⁻¹' range g
  have hA : IsClosed A := (isCompact_range f.continuous).isClosed.preimage continuous_subtype_val
  have hB : IsClosed B := (isCompact_range g.continuous).isClosed.preimage continuous_subtype_val
  have hcover : A ∪ B = univ := by
    ext x
    exact ⟨fun _ => mem_univ _, fun _ => x.property⟩
  have hagree : ∀ x : U, x ∈ A → x ∈ B → r x.1 = q x.1 := by
    intro x hxa hxb
    rcases mem_insert_iff.mp (hinter ⟨hxa, hxb⟩) with heq | heq
    · rw [heq, hrf, h0, hqg]
    · rw [mem_singleton_iff.mp heq, hrf, h1, hqg]
  let τ : U → unitInterval := fun x => if x ∈ A then r x.1 else q x.1
  have hτA : ContinuousOn τ A := by
    have h : ContinuousOn (fun x : U => r x.1) A :=
      hr.comp continuous_subtype_val.continuousOn (fun _ hx => hx)
    exact h.congr (fun x hx => by simp only [τ, hx, ↓reduceIte])
  have hτB : ContinuousOn τ B := by
    have h : ContinuousOn (fun x : U => q x.1) B :=
      hq.comp continuous_subtype_val.continuousOn (fun _ hx => hx)
    apply h.congr
    intro x hx
    by_cases hxA : x ∈ A
    · simp only [τ, hxA, ↓reduceIte]
      exact hagree x hxA hx
    · simp only [τ, hxA, ↓reduceIte]
  have hτ : Continuous τ := by
    rw [← continuousOn_univ, ← hcover]
    exact hτA.union_of_isClosed hτB hA hB
  refine ⟨⟨τ, hτ⟩, ?_, ?_⟩
  · intro t
    change (if (⟨f t, Or.inl (mem_range_self t)⟩ : U) ∈ A then _ else _) = t
    have htA : (⟨f t, Or.inl (mem_range_self t)⟩ : U) ∈ A := mem_range_self t
    simp only [htA, ↓reduceIte, hrf]
  · intro t
    change (if (⟨g t, Or.inr (mem_range_self t)⟩ : U) ∈ A then _ else _) = t
    by_cases htA : (⟨g t, Or.inr (mem_range_self t)⟩ : U) ∈ A
    · simp only [htA, ↓reduceIte]
      exact (hagree ⟨g t, Or.inr (mem_range_self t)⟩ htA (mem_range_self t)).trans (hqg t)
    · simp only [htA, ↓reduceIte, hqg]

/-- The circle formed by two homotopic arcs is null-homotopic. This supplies the
enclosing-disc step used in Graph Minors VI, Section 4, page 124. -/
theorem isNullHomotopicOArc_of_homotopic_arcs
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (f g : Curve S) (hf : f.IsLine) (hg : g.IsLine)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hinter : range f ∩ range g ⊆ {f 0, f 1})
    (hhom : CurvesHomotopic f g) :
    IsNullHomotopicOArc (range f ∪ range g) := by
  classical
  have hmeet : ∀ s t, f s = g t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t heq
    have hmem := hinter ⟨mem_range_self s, ⟨t, heq.symm⟩⟩
    rcases mem_insert_iff.mp hmem with he | he
    · exact Or.inl ⟨hf he, hg (heq.symm.trans (he.trans h0))⟩
    · have he := mem_singleton_iff.mp he
      exact Or.inr ⟨hf he, hg (heq.symm.trans (he.trans h1))⟩
  obtain ⟨φ⟩ := oArc_of_two_arcs ⟨f.continuous, hf⟩ ⟨g.continuous, hg⟩ h0 h1 hmeet
  obtain ⟨τ, hτf, hτg⟩ := exists_common_arc_parameter f g hf hg h0 h1 hinter
  let U := range f ∪ range g
  have hfr : ∀ x : U, x.1 ∈ range f → f (τ x) = x.1 := by
    intro x hx
    obtain ⟨t, ht⟩ := hx
    have heq : x = ⟨f t, Or.inl (mem_range_self t)⟩ := Subtype.ext ht.symm
    rw [heq, hτf]
  have hgr : ∀ x : U, x.1 ∈ range g → g (τ x) = x.1 := by
    intro x hx
    obtain ⟨t, ht⟩ := hx
    have heq : x = ⟨g t, Or.inr (mem_range_self t)⟩ := Subtype.ext ht.symm
    rw [heq, hτg]
  obtain ⟨H, _, hH0, hH1, hleft, _, hright, _⟩ := hhom
  have hfixed : ∀ x : U, x.1 ∈ range f → x.1 ∈ range g →
      ∀ t, H (τ x, t) = g (τ x) := by
    intro x hx hy t
    rcases mem_insert_iff.mp (hinter ⟨hx, hy⟩) with he | he
    · have hτ0 : τ x = 0 := hf ((hfr x hx).trans he)
      rw [hτ0, hleft, h0]
    · have hτ1 : τ x = 1 := hf ((hfr x hx).trans (mem_singleton_iff.mp he))
      rw [hτ1, hright, h1]
  let A : Set (Circle × unitInterval) := {p | (φ p.1).1 ∈ range f}
  let B : Set (Circle × unitInterval) := {p | (φ p.1).1 ∈ range g}
  have hval : Continuous (fun p : Circle × unitInterval => (φ p.1).1) :=
    continuous_subtype_val.comp (φ.continuous.comp continuous_fst)
  have hA : IsClosed A := (isCompact_range f.continuous).isClosed.preimage hval
  have hB : IsClosed B := (isCompact_range g.continuous).isClosed.preimage hval
  have hcover : A ∪ B = univ := by
    ext p
    exact ⟨fun _ => mem_univ _, fun _ => (φ p.1).property⟩
  let K : Circle × unitInterval → S := fun p =>
    if p ∈ A then H (τ (φ p.1), p.2) else g (τ (φ p.1))
  have hfirst : Continuous (fun p : Circle × unitInterval => H (τ (φ p.1), p.2)) := by
    fun_prop
  have hsecond : Continuous (fun p : Circle × unitInterval => g (τ (φ p.1))) := by
    fun_prop
  have hKA : ContinuousOn K A := by
    apply hfirst.continuousOn.congr
    intro p hp
    simp only [K, hp, ↓reduceIte]
  have hKB : ContinuousOn K B := by
    apply hsecond.continuousOn.congr
    intro p hp
    by_cases hpA : p ∈ A
    · simp only [K, hpA, ↓reduceIte]
      exact hfixed (φ p.1) hpA hp p.2
    · simp only [K, hpA, ↓reduceIte]
  have hK : Continuous K := by
    rw [← continuousOn_univ, ← hcover]
    exact hKA.union_of_isClosed hKB hA hB
  let γ : C(Circle, S) :=
    ⟨fun w => g (τ (φ w)), g.continuous.comp (τ.continuous.comp φ.continuous)⟩
  have hK0 : ∀ w, K (w, 0) = (φ w).1 := by
    intro w
    by_cases hw : (φ w).1 ∈ range f
    · change (if (w, 0) ∈ A then _ else _) = _
      have hwA : (w, (0 : unitInterval)) ∈ A := hw
      simp only [hwA, ↓reduceIte, hH0]
      exact hfr (φ w) hw
    · change (if (w, 0) ∈ A then _ else _) = _
      have hwA : (w, (0 : unitInterval)) ∉ A := hw
      simp only [hwA, ↓reduceIte]
      exact hgr (φ w) ((φ w).property.resolve_left hw)
  have hK1 : ∀ w, K (w, 1) = γ w := by
    intro w
    dsimp only [K, γ, ContinuousMap.coe_mk]
    split_ifs <;> simp only [hH1]
  have hfirstHom : ClosedCurvesHomotopicIn univ
      ⟨fun w => (φ w).1, continuous_subtype_val.comp φ.continuous⟩ γ :=
    ⟨⟨K, hK⟩, fun _ => mem_univ _, hK0, hK1⟩
  let σ : C(Circle × unitInterval, unitInterval) :=
    ⟨fun p => ⟨(1 - (p.2 : ℝ)) * (τ (φ p.1) : ℝ),
      mul_nonneg (sub_nonneg.mpr p.2.2.2) (τ (φ p.1)).2.1,
      by nlinarith [p.2.2.1, p.2.2.2, (τ (φ p.1)).2.1, (τ (φ p.1)).2.2]⟩,
      by fun_prop⟩
  have hσ0 : ∀ w, σ (w, 0) = τ (φ w) := by intro w; ext; simp [σ]
  have hσ1 : ∀ w, σ (w, 1) = 0 := by intro w; ext; simp [σ]
  have hγnull : ClosedCurveIsNullHomotopicIn univ γ := by
    refine ⟨g 0, mem_univ _, g.comp σ, fun _ => mem_univ _, ?_, ?_⟩
    · intro w
      change g (σ (w, 0)) = g (τ (φ w))
      rw [hσ0]
    · intro w
      change g (σ (w, 1)) = g 0
      rw [hσ1]
  exact ⟨φ, GM07.closedCurveIsNullHomotopicIn_of_homotopic hfirstHom hγnull⟩

/-- A path and a cuff arc in the same homotopy class enclose a closed disc when
they meet only at their ends. This is the enclosed portion used to define
`P(s,t,S)` in Graph Minors VI, Section 4, page 124. -/
theorem exists_enclosedDisc_of_pathHomotopicToArc
    {S : Type u} [TopologicalSpace S] {P : Drawing S} {s t : S} {A : Set S}
    (hS : IsSurface S) (hPA : PathHomotopicToArc P s t A)
    (hinter : P.U ∩ closure A ⊆ {s, t}) :
    ∃ Δ : Set S, IsEnclosedDisc P A Δ := by
  let : T2Space S := hS.2.1
  obtain ⟨f, g, hf, hg, hfg⟩ := hPA
  have h0 : f 0 = g 0 := hf.2.2.1.trans hg.2.2.1.symm
  have h1 : f 1 = g 1 := hf.2.2.2.trans hg.2.2.2.symm
  have hi : range f ∩ range g ⊆ {f 0, f 1} := by
    rw [hf.2.1, hg.2.1, hf.2.2.1, hf.2.2.2]
    exact hinter
  have hnull := isNullHomotopicOArc_of_homotopic_arcs f g hf.1 hg.1 h0 h1 hi hfg
  rw [hf.2.1, hg.2.1] at hnull
  have hO : IsOArc (P.U ∪ closure A) := by
    obtain ⟨φ, _⟩ := hnull
    exact ⟨φ⟩
  obtain ⟨Δ, hΔ, hbd⟩ := GM07.nullHomotopicOArc_bounds_disc hS hO hnull
  refine ⟨Δ, hΔ, ?_, hbd⟩
  intro x hx
  apply discBd_subset Δ
  rw [hbd]
  exact Or.inr (subset_closure hx)

end GraphMinor.GM06
