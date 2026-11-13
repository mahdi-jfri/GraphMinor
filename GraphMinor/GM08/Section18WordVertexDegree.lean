module

public import GraphMinor.Surface.CutEdges
import GraphMinor.GM08.Section18WordCutVertexCount
import GraphMinor.GM08.Section18WordCutEnds
import GraphMinor.GM08.Section18WordIncidentEnds
import Lean.Elab.Tactic.Omega

/-!
# The vertex fibre size equals the cut degree

The two side ends of every incident cut edge and the two ends of the
old boundary account for all free ends at a vertex. Each lifted vertex
uses two of these ends. Hence an interior vertex has one lift for each
incident cut edge, and a boundary vertex has one further lift. This is
the local vertex formula in the proof of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

private theorem cancel_twice (n d b : ℕ) (h : 2 * n = 2 * d + 2 * b) : n = d + b := by
  omega

open Classical in
/-- The exact vertex fibre formula for the constructed word cut in
VIII (18.2), page 286. Every cut edge has its middle off the boundary.
A vertex touched by the cut has one lift per incident cut edge, with
one additional lift when it lies on the old boundary. -/
theorem word_cut_vertex_fibre_eq_degree {S Y : Type u} [TopologicalSpace S]
    [TopologicalSpace Y] [T2Space S] [T2Space Y]
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {D : Set (Set S)} (hDE : D ⊆ E)
    (hmid : ∀ e ∈ D, edgeMid A e ∉ bd S)
    {g : ℕ × ℂ → Y} (hg : Presents (cutW W (lab '' D)) g) {ψ : Y → S}
    (hψ : ∀ a ∈ Dsk W, ψ (g a) = f a) {v : S} (hv : v ∈ V) (hvD : v ∈ ⋃₀ D) :
    (ψ ⁻¹' {v}).ncard = {e ∈ D | v ∈ e}.ncard + if v ∈ bd S then 1 else 0 := by
  classical
  have : Finite (SE W) := finite_se hw.fin
  have hdegfin : {e ∈ D | v ∈ e}.Finite :=
    (hw.graph.fine.subset hDE).subset (sep_subset _ _)
  obtain ⟨e, he, hve⟩ := hvD
  have hdegpos : 0 < {e ∈ D | v ∈ e}.ncard := (ncard_pos hdegfin).mpr ⟨e, he, hve⟩
  let N : Set (SE W) := {a | f (spe W a) = v ∧
    ∃ e ∈ D, ∃ ε, (W a.1.1)[a.1.2.1]? = some (lab e, ε)}
  have hNcount : N.ncard = 2 * {e ∈ D | v ∈ e}.ncard := word_new_cut_ends_ncard hw hDE hmid hv
  have hNpos : 0 < N.ncard := by rw [hNcount]; exact Nat.mul_pos (by decide) hdegpos
  obtain ⟨c, hcv, d, hd, ε, hlabel⟩ := (ncard_pos (toFinite N)).mp hNpos
  have hc : prtL W (lab '' D) c = c :=
    (prtL_eq_iff hw.paired c hlabel).mpr (Or.inl (mem_image_of_mem lab hd))
  have hvE : v ∈ ⋃₀ E := ⟨e, hDE he, hve⟩
  have hdouble := word_cut_vertex_fibre_count hw hg hψ c hc
    (hcv.symm ▸ (show v ∈ V ∩ ⋃₀ E from ⟨hv, hvE⟩))
  rw [hcv] at hdouble
  have hsplit := word_cut_fixed_ends_ncard hw hDE hmid hv
  rw [word_new_cut_ends_ncard hw hDE hmid hv] at hsplit
  have htotal := hdouble.symm.trans hsplit
  by_cases hbd : v ∈ bd S
  · simp only [ite_eq_left hbd] at htotal ⊢
    exact cancel_twice _ _ 1 htotal
  · simp only [ite_eq_right hbd] at htotal ⊢
    exact cancel_twice _ _ 0 htotal

end GraphMinor.GM08
