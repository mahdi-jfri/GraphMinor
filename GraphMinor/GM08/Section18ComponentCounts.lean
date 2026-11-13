module

public import GraphMinor.Surface.Dissection
import GraphMinor.Surface.TriPath
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counts on the two sides of a component partition

Every edge and face lies on one side of an open-and-closed partition.
The finite counts therefore split into the counts on each side. This
is the additivity used for the component Euler characteristics in the
proof of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

private theorem connected_side {T : Type} [TopologicalSpace T]
    {U A : Set T} (hU : IsClopen U) (hA : IsPreconnected A) :
    A ⊆ U ∨ A ⊆ Uᶜ :=
  IsPreconnected.subset_or_subset hU.2 hU.1.isOpen_compl disjoint_compl_right
    (by simp) hA

/-- Vertex, edge, and face counts of a dissection add over a partition
into open-and-closed parts, as used in VIII (18.2), page 286. -/
theorem dissection_counts_split_clopen {T : Type} [TopologicalSpace T] [T2Space T]
    {U V : Set T} (hU : IsClopen U) {E 𝓕 : Set (Set T)} (hd : IsDissection V E 𝓕) :
    (V ∩ ⋃₀ E).ncard = ((V ∩ ⋃₀ E) ∩ U).ncard + ((V ∩ ⋃₀ E) ∩ Uᶜ).ncard ∧
    E.ncard = {e ∈ E | e ⊆ U}.ncard + {e ∈ E | e ⊆ Uᶜ}.ncard ∧
    𝓕.ncard = {Φ ∈ 𝓕 | Φ ⊆ U}.ncard + {Φ ∈ 𝓕 | Φ ⊆ Uᶜ}.ncard := by
  have split : ∀ (B : Set (Set T)), B.Finite →
      (∀ A ∈ B, A.Nonempty ∧ (A ⊆ U ∨ A ⊆ Uᶜ)) →
      B.ncard = {A ∈ B | A ⊆ U}.ncard + {A ∈ B | A ⊆ Uᶜ}.ncard := by
    intro B hB hside
    have heq : B = {A ∈ B | A ⊆ U} ∪ {A ∈ B | A ⊆ Uᶜ} := by
      ext A
      constructor
      · intro hA
        exact (hside A hA).2.imp (fun h => ⟨hA, h⟩) (fun h => ⟨hA, h⟩)
      · exact fun h => h.elim And.left And.left
    have hdis : Disjoint {A ∈ B | A ⊆ U} {A ∈ B | A ⊆ Uᶜ} := by
      refine disjoint_left.mpr ?_
      intro A hA hA'
      obtain ⟨x, hx⟩ := (hside A hA.1).1
      exact hA'.2 hx (hA.2 hx)
    exact (congrArg ncard heq).trans
      (ncard_union_eq hdis (hB.subset (sep_subset _ _)) (hB.subset (sep_subset _ _)))
  refine ⟨?_, split E hd.graph.fine ?_, split 𝓕 hd.fin ?_⟩
  · have h := ncard_inter_add_ncard_sdiff_eq_ncard (V ∩ ⋃₀ E) U
      (hd.graph.fin.subset inter_subset_left)
    simpa only [sdiff_eq_compl_inter, inter_comm Uᶜ] using h.symm
  · intro e he
    obtain ⟨a, b, _, hl, _⟩ := hd.graph.edge e he
    exact ⟨⟨a, hl.left_mem⟩, connected_side hU hl.isPreconnected_self⟩
  · intro Φ hΦ
    have hD := hd.disc Φ hΦ
    have hcl : closure (discInt Φ) = Φ :=
      subset_antisymm (closure_minimal (discInt_subset Φ) hD.isClosed) hD.subset_closure_discInt
    have hconn : IsPreconnected Φ := hcl ▸ hD.isPreconnected_discInt.closure
    exact ⟨hD.discInt_nonempty.mono (discInt_subset Φ), connected_side hU hconn⟩

end GraphMinor.GM08
