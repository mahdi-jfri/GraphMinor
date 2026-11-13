module

public import GraphMinor.GM12.Section3FiniteReroute
public import GraphMinor.GM12.Section3PathConcatenation

/-!
# The global homotopy of the finite rerouting

For the circle-intersection step used by XII (3.1), page 245, concatenate
the finite local replacements. Their fixed-end homotopies give a homotopy
of the original path. The resulting path lies in the solid set together
with finitely many outer pieces of the original subpaths. Each such
piece meets the solid set only at its attachment endpoint. This keeps
both the original carrier inclusion and the relevant homotopy class.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A path can be rerouted up to homotopy so that its new material
off a fixed solid set consists of finitely many original outer
subpaths, each meeting the solid set at most at one endpoint. -/
theorem exists_global_homotopic_reroute
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsSolid F) {a b : S} (p : Path a b) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval) (s u : Fin n → unitInterval) (q : Path a b),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧ p.Homotopic q ∧
      F ∪ range q ⊆ F ∪ {p 0} ∪ ⋃ i : Fin n,
        (range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∪
          range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1)) ∧
      ∀ i : Fin n, s i ≤ u i ∧
        range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∩ F ⊆
          {(p.subpath (t i.castSucc) (t i.succ)) (s i)} ∧
        range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1) ∩ F ⊆
          {(p.subpath (t i.castSucc) (t i.succ)) (u i)} := by
  obtain ⟨n, t, s, u, r, ht0, htlast, hmono, hpieces⟩ := exists_finite_homotopic_reroutes hS hF p
  obtain ⟨q, hpq, hq⟩ := exists_homotopic_path_of_piecewise_reroutes p t ht0 htlast r
    (fun i => (hpieces i).2.1)
  refine ⟨n, t, s, u, q, ht0, htlast, hmono, hpq, ?_,
    fun i => ⟨(hpieces i).1, (hpieces i).2.2.2.1, (hpieces i).2.2.2.2⟩⟩
  intro x hx
  rcases hx with hxF | hxq
  · exact Or.inl (Or.inl hxF)
  rcases hq hxq with hx0 | hxr
  · exact Or.inl (Or.inr hx0)
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxr
  have heq := (hpieces i).2.2.1
  have hxparts : x ∈ F ∪ range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∪
      range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1) :=
    heq ▸ (show x ∈ F ∪ range (r i) from Or.inr hxi)
  rcases hxparts with (hxF | hxL) | hxR
  · exact Or.inl (Or.inl hxF)
  · exact Or.inr (mem_iUnion.mpr ⟨i, Or.inl hxL⟩)
  · exact Or.inr (mem_iUnion.mpr ⟨i, Or.inr hxR⟩)

end GraphMinor.GM12
