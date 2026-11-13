module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.Section14
import GraphMinor.GM08.Section15Tube

/-!
# Isomorphic grafts with different vertex label types

A graft isomorphism gives a simulation by singleton branch sets. Edge
labels use the same ambient type, so the unused edge values need no
extra choices. This lets the proof of (15.4) enlarge a finite vertex
label type and then transfer its comparisons back.
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v w

/-- A graft isomorphism between different vertex label types, with the
same edge type, gives a simulation. This removes the infinite-label
convention from the conclusion of VIII (15.4), page 282. -/
theorem isGraftSimulatedIn_of_isGraftIso_same_edges {α : Type u} {γ : Type w} {β : Type v}
    {Y : Graft γ β} {X : Graft α β} (h : IsGraftIso Y X) : IsGraftSimulatedIn Y X := by
  classical
  have hindex : Y.index = X.index := Graft.index_eq_of_isGraftIso h
  obtain ⟨φ, hT⟩ := h
  let ηv : γ → Set α := fun u => if hu : u ∈ V(Y.G) then {(φ.vertexEquiv ⟨u, hu⟩).1} else ∅
  let ηe : β → β := fun e => if he : e ∈ E(Y.G) then (φ.edgeEquiv ⟨e, he⟩).1 else e
  have hηv_eq : ∀ {u : γ} (hu : u ∈ V(Y.G)), ηv u = {(φ.vertexEquiv ⟨u, hu⟩).1} :=
    fun hu => by simp [ηv, hu]
  have hηe_eq : ∀ {e : β} (he : e ∈ E(Y.G)), ηe e = (φ.edgeEquiv ⟨e, he⟩).1 :=
    fun he => by simp [ηe, he]
  refine ⟨ηv, ηe, ?_, ?_, ?_⟩
  · refine {
      vertex_nonempty := fun u hu => by
        rw [hηv_eq hu]
        exact singleton_nonempty _
      vertex_subset := fun u hu x hx => by
        rw [hηv_eq hu, mem_singleton_iff] at hx
        exact hx ▸ (φ.vertexEquiv ⟨u, hu⟩).2
      edge_mem := fun e he => by
        rw [hηe_eq he]
        exact (φ.edgeEquiv ⟨e, he⟩).2
      vertex_disjoint := fun u₁ hu₁ u₂ hu₂ hne => by
        rw [hηv_eq hu₁, hηv_eq hu₂, disjoint_singleton]
        intro heq
        apply hne
        have hsub : φ.vertexEquiv ⟨u₁, hu₁⟩ = φ.vertexEquiv ⟨u₂, hu₂⟩ := Subtype.ext heq
        exact congrArg Subtype.val (φ.vertexEquiv.injective hsub)
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
        rw [hηe_eq he₁, hηe_eq he₂] at heq
        have hsub : φ.edgeEquiv ⟨e₁, he₁⟩ = φ.edgeEquiv ⟨e₂, he₂⟩ := Subtype.ext heq
        exact congrArg Subtype.val (φ.edgeEquiv.injective hsub)
      inc_iff := fun u hu e he => by
        rw [hηv_eq hu, hηe_eq he]
        simp only [mem_singleton_iff, exists_eq_left]
        constructor
        · rintro ⟨w, hlink⟩
          have hw : w ∈ V(Y.G) := hlink.right_mem
          have hlink' := (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨w, hw⟩).mp hlink
          exact hlink'.inc_left
        · rintro ⟨x, hlink'⟩
          have hx : x ∈ V(X.G) := hlink'.right_mem
          let w := φ.vertexEquiv.symm ⟨x, hx⟩
          have hlink : Y.G.IsLink e u w.1 := by
            have := (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ w).mpr
              (by simpa [w] using hlink')
            exact this
          exact hlink.inc_left
      isLoopAt_iff := fun u hu e he => by
        rw [hηv_eq hu, hηe_eq he]
        simp only [mem_singleton_iff]
        constructor
        · intro hloop x ⟨y, hl⟩
          have hl_loop : X.G.IsLink (φ.edgeEquiv ⟨e, he⟩).1
              (φ.vertexEquiv ⟨u, hu⟩).1 (φ.vertexEquiv ⟨u, hu⟩).1 :=
            (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨u, hu⟩).mp hloop
          rcases hl.eq_and_eq_or_eq_and_eq hl_loop with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
        · intro hall
          have heX : (φ.edgeEquiv ⟨e, he⟩).1 ∈ E(X.G) := (φ.edgeEquiv ⟨e, he⟩).2
          obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet heX
          have hx := hall x hl.inc_left
          have hy := hall y hl.inc_right
          subst hx hy
          exact (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨u, hu⟩).mpr hl
      connected := fun u hu => by
        let x₀ := (φ.vertexEquiv ⟨u, hu⟩).1
        have hx₀_mem : x₀ ∈ V(X.G.deleteEdges (ηe '' E(Y.G))) := (φ.vertexEquiv ⟨u, hu⟩).2
        let K := (X.G.deleteEdges (ηe '' E(Y.G))).induce {x₀}
        have hK_le : K ≤ X.G.deleteEdges (ηe '' E(Y.G)) :=
          (X.G.deleteEdges (ηe '' E(Y.G))).induce_le (singleton_subset_iff.mpr hx₀_mem)
        have hVK : V(K) = ηv u := by
          rw [vertexSet_induce, hηv_eq hu]
        refine ⟨K, hK_le, hVK, ⟨x₀, by simp [K]⟩, ?_⟩
        intro a ha b hb
        rw [vertexSet_induce, mem_singleton_iff] at ha hb
        subst ha hb
        exact Relation.ReflTransGen.refl }
  · exact hindex.symm
  · intro u hu
    have huV : u ∈ V(Y.G) := Y.T_subset hu
    refine ⟨(φ.vertexEquiv ⟨u, huV⟩).1, ?_, (hT ⟨u, huV⟩).mp hu⟩
    rw [hηv_eq huV]
    exact mem_singleton _

end GraphMinor.GM08
