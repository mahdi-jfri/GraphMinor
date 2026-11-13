module

public import GraphMinor.Surface.CutEdges
import Mathlib.Data.Set.Card.Arithmetic

/-!
# The contribution of incident cut edges

At a graph vertex, each incident cut edge contributes two side ends,
one from each side of the edge. Different edges have different labels,
so their contributions are disjoint. This counts the new free ends in
the vertex calculation of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

private theorem incident_edge_end_count {S : Type u} [TopologicalSpace S] [T2Space S]
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {e : Set S} (he : e ∈ E)
    (hmid : edgeMid A e ∉ bd S) {v : S} (hv : v ∈ V) (hve : v ∈ e) :
    {a : SE W | f (spe W a) = v ∧
      ∃ ε, (W a.1.1)[a.1.2.1]? = some (lab e, ε)}.ncard = 2 := by
  obtain ⟨i, p, j, q, ε₁, ε₂, h₁, h₂, hne⟩ := hw.exists_sides he hmid
  let s : EdgeSides W (lab e) i p j q ε₁ ε₂ := ⟨h₁, h₂, hne⟩
  have hend : ∃ τ, extI (A e) (eo τ) = v := by
    have hh : v ∈ ({A e 0, A e 1} : Set S) := (hw.arc e he).2.2 ▸ ⟨hve, hv⟩
    rcases hh with hh | hh
    · refine ⟨false, ?_⟩
      have hz : extI (A e) (eo false) = A e 0 := by simpa [eo] using extI_coe (A e) 0
      exact hz.trans hh.symm
    · refine ⟨true, ?_⟩
      have hz : extI (A e) (eo true) = A e 1 := by simpa [eo] using extI_coe (A e) 1
      exact hz.trans hh.symm
  obtain ⟨τ, hτ⟩ := hend
  have hdistinct : s.end₁ τ ≠ s.end₂ τ := by
    intro hh
    exact hne (congrArg (fun a : SE W => (a.1.1, a.1.2.1)) hh)
  have heq : {a : SE W | f (spe W a) = v ∧
      ∃ ε, (W a.1.1)[a.1.2.1]? = some (lab e, ε)} = {s.end₁ τ, s.end₂ τ} := by
    ext a
    constructor
    · rintro ⟨hav, ε, hlabel⟩
      obtain ⟨τ', ha | ha⟩ := s.mem hw.paired a hlabel
      · have heτ : τ' = τ := hw.eo_inj he (by rw [← hw.f_end₁ he s τ', ← ha, hav, hτ])
        exact Or.inl (heτ ▸ ha)
      · have heτ : τ' = τ := hw.eo_inj he (by rw [← hw.f_end₂ he s τ', ← ha, hav, hτ])
        exact Or.inr (heτ ▸ ha)
    · rintro (rfl | rfl)
      · exact ⟨(hw.f_end₁ he s τ).trans hτ, ε₁, h₁⟩
      · exact ⟨(hw.f_end₂ he s τ).trans hτ, ε₂, h₂⟩
  rw [heq, ncard_pair hdistinct]

/-- Each incident cut edge contributes two new free side ends in the
word cut, as counted in VIII (18.2), page 286. All cut edges have their
middles off the boundary. -/
theorem word_new_cut_ends_ncard {S : Type u} [TopologicalSpace S] [T2Space S]
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {D : Set (Set S)} (hDE : D ⊆ E)
    (hmid : ∀ e ∈ D, edgeMid A e ∉ bd S) {v : S} (hv : v ∈ V) :
    {a : SE W | f (spe W a) = v ∧
      ∃ e ∈ D, ∃ ε, (W a.1.1)[a.1.2.1]? = some (lab e, ε)}.ncard =
      2 * {e ∈ D | v ∈ e}.ncard := by
  classical
  have : Finite (SE W) := finite_se hw.fin
  let I : Set (Set S) := {e ∈ D | v ∈ e}
  let ends : Set S → Set (SE W) := fun e => {a | f (spe W a) = v ∧
    ∃ ε, (W a.1.1)[a.1.2.1]? = some (lab e, ε)}
  have hIfin : I.Finite := (hw.graph.fine.subset hDE).subset (sep_subset _ _)
  have hcount : ∀ e ∈ I, (ends e).ncard = 2 :=
    fun e he => incident_edge_end_count hw (hDE he.1) (hmid e he.1) hv he.2
  have hunion : {a : SE W | f (spe W a) = v ∧
      ∃ e ∈ D, ∃ ε, (W a.1.1)[a.1.2.1]? = some (lab e, ε)} = ⋃ e ∈ I, ends e := by
    ext a
    constructor
    · rintro ⟨hav, e, he, ε, hlabel⟩
      obtain ⟨i, p, j, q, ε₁, ε₂, h₁, h₂, hne⟩ := hw.exists_sides (hDE he) (hmid e he)
      let s : EdgeSides W (lab e) i p j q ε₁ ε₂ := ⟨h₁, h₂, hne⟩
      obtain ⟨τ, ha | ha⟩ := s.mem hw.paired a hlabel
      · have hve : v ∈ e := by rw [← hav, ha, hw.f_end₁ (hDE he) s τ]; exact hw.extI_mem (hDE he) _
        exact mem_iUnion₂.mpr ⟨e, ⟨he, hve⟩, hav, ε, hlabel⟩
      · have hve : v ∈ e := by rw [← hav, ha, hw.f_end₂ (hDE he) s τ]; exact hw.extI_mem (hDE he) _
        exact mem_iUnion₂.mpr ⟨e, ⟨he, hve⟩, hav, ε, hlabel⟩
    · intro ha
      obtain ⟨e, he, hav, ε, hlabel⟩ := mem_iUnion₂.mp ha
      exact ⟨hav, e, he.1, ε, hlabel⟩
  have hdis : I.PairwiseDisjoint ends := by
    intro e he d hd hne
    apply disjoint_left.mpr
    rintro a ⟨_, ε, h₁⟩ ⟨_, δ, h₂⟩
    have hlabel : lab e = lab d := congrArg Prod.fst (Option.some.inj (h₁.symm.trans h₂))
    exact hne (hw.lab_inj (hDE he.1) (hDE hd.1) hlabel)
  rw [hunion, hIfin.ncard_biUnion (fun _ _ => toFinite _) hdis]
  rw [finsum_mem_eq_finite_toFinset_sum _ hIfin]
  have hsum : (∑ e ∈ hIfin.toFinset, (ends e).ncard) = ∑ _e ∈ hIfin.toFinset, 2 := by
    apply Finset.sum_congr rfl
    intro e he
    exact hcount e (hIfin.mem_toFinset.mp he)
  rw [hsum]
  simp only [Finset.sum_const, smul_eq_mul]
  rw [Set.ncard_eq_toFinset_card I hIfin, Nat.mul_comm]

end GraphMinor.GM08
