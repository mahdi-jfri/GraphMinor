module

public import GraphMinor.Surface.CutEdges
import GraphMinor.GM08.Section18WordBoundaryEnds
import Mathlib.Data.Set.Card

/-!
# Separating new and old free ends

At a cut vertex, a free end either comes from an edge that was cut or
was already on the surface boundary. These alternatives are disjoint
because every cut edge has its middle in the surface interior. This
separates the two terms in the vertex count for VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

open Classical in
/-- Free side ends after cutting split into the new cut-edge ends and
the two old boundary ends, if the vertex is on the boundary. This is the
local count used by VIII (18.2), page 286. -/
theorem word_cut_fixed_ends_ncard {S : Type u} [TopologicalSpace S] [T2Space S]
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {D : Set (Set S)} (hDE : D ⊆ E)
    (hmid : ∀ e ∈ D, edgeMid A e ∉ bd S) {v : S} (hv : v ∈ V) :
    {a : SE W | f (spe W a) = v ∧ prtL W (lab '' D) a = a}.ncard =
      {a : SE W | f (spe W a) = v ∧
        ∃ e ∈ D, ∃ ε, (W a.1.1)[a.1.2.1]? = some (lab e, ε)}.ncard +
      if v ∈ bd S then 2 else 0 := by
  classical
  have : Finite (SE W) := finite_se hw.fin
  let N : Set (SE W) := {a | f (spe W a) = v ∧
    ∃ e ∈ D, ∃ ε, (W a.1.1)[a.1.2.1]? = some (lab e, ε)}
  let B : Set (SE W) := {a | f (spe W a) = v ∧ prtL W ∅ a = a}
  have hget : ∀ a : SE W, ∃ k ε, (W a.1.1)[a.1.2.1]? = some (k, ε) :=
    fun a => ⟨_, _, List.getElem?_eq_getElem a.2⟩
  have hdis : Disjoint N B := by
    apply disjoint_left.mpr
    rintro a ⟨_, e, he, ε, hlabel⟩ ⟨_, hfixed⟩
    have hfree : FreeSide W a.1.1 a.1.2.1 :=
      ((prtL_eq_iff hw.paired a hlabel).mp hfixed).resolve_left (notMem_empty _)
    obtain ⟨i, p, j, q, ε₁, ε₂, h₁, h₂, hne⟩ := hw.exists_sides (hDE he) (hmid e he)
    exact hne ((hfree i p (lab e) ε ε₁ hlabel h₁).symm.trans
      (hfree j q (lab e) ε ε₂ hlabel h₂))
  have heq : {a : SE W | f (spe W a) = v ∧ prtL W (lab '' D) a = a} = N ∪ B := by
    ext a
    constructor
    · rintro ⟨hav, hfixed⟩
      obtain ⟨k, ε, hlabel⟩ := hget a
      rcases (prtL_eq_iff hw.paired a hlabel).mp hfixed with hcut | hfree
      · obtain ⟨e, he, rfl⟩ := hcut
        exact Or.inl ⟨hav, e, he, ε, hlabel⟩
      · exact Or.inr ⟨hav, (prtL_eq_iff hw.paired a hlabel).mpr (Or.inr hfree)⟩
    · rintro (⟨hav, e, he, ε, hlabel⟩ | ⟨hav, hfixed⟩)
      · exact ⟨hav, (prtL_eq_iff hw.paired a hlabel).mpr
          (Or.inl (mem_image_of_mem lab he))⟩
      · obtain ⟨k, ε, hlabel⟩ := hget a
        have hfree : FreeSide W a.1.1 a.1.2.1 :=
          ((prtL_eq_iff hw.paired a hlabel).mp hfixed).resolve_left (notMem_empty _)
        exact ⟨hav, (prtL_eq_iff hw.paired a hlabel).mpr (Or.inr hfree)⟩
  rw [heq, ncard_union_eq hdis (toFinite N) (toFinite B)]
  exact congrArg (fun n => N.ncard + n) (word_free_ends_at_vertex_ncard hw hv)

end GraphMinor.GM08
