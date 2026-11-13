module

public import GraphMinor.Crossing.PlanarEuler

/-!
# Euler's bound for planar graphs without triangles

A plane graph on `n ≥ 3` vertices with no triangle has at most `2 n - 4` edges
(`triangleFree_edgesOn_ncard_le`). The proof is the one of `bipartite_edgesOn_ncard_le` in
`Crossing/PlanarEuler.lean`: each face is bounded by a cycle, which now has at least four vertices,
and each edge lies on at most two faces.
-/

@[expose] public section

namespace GraphMinor.Wagner

open SimpleGraph Set GraphMinor.HP25 GraphMinor.Crossing GraphMinor.HP25.PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-- A cycle of a graph with no triangle on `R` has at least four vertices. -/
theorem isCycleList_four_le_length_of_noTriangle
    (htf : ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, G.Adj a b → G.Adj b c → G.Adj c a → False) {C : List V}
    (hC : IsCycleList G C) (hCR : ∀ x ∈ C, x ∈ R) : 4 ≤ C.length := by
  have h3 := hC.1
  by_contra hlt
  have hlen : C.length = 3 := by omega
  rcases C with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> try (simp at hlen)
  have hab : G.Adj a b := hC.2.2 (a, b) (by simp [List.rotate])
  have hbc : G.Adj b c := hC.2.2 (b, c) (by simp [List.rotate])
  have hca : G.Adj c a := hC.2.2 (c, a) (by simp [List.rotate])
  exact htf a (hCR a (by simp)) b (hCR b (by simp)) c (hCR c (by simp)) hab hbc hca

/-- Double counting on a finite relation `r : α → β → Prop` (a copy of the private lemma
`bipartite_ncard_mul_le` of `Crossing/PlanarEuler.lean`). -/
theorem ncard_mul_le_of_rel {α β : Type*} {F : Set α} {E : Set β} (r : α → β → Prop)
    (hF : F.Finite) (hE : E.Finite) (k m : ℕ)
    (hleft : ∀ f ∈ F, k ≤ {e ∈ E | r f e}.ncard)
    (hright : ∀ e ∈ E, {f ∈ F | r f e}.ncard ≤ m) :
    k * F.ncard ≤ m * E.ncard := by
  classical
  let sF := hF.toFinset
  let sE := hE.toFinset
  have hFcard : F.ncard = sF.card := ncard_eq_toFinset_card F hF
  have hEcard : E.ncard = sE.card := ncard_eq_toFinset_card E hE
  have hL : ∀ f ∈ sF, k ≤ ∑ e ∈ sE, (if r f e then 1 else 0) := by
    intro f hf
    rw [← Finset.card_filter]
    have hfF : f ∈ F := hF.mem_toFinset.mp hf
    have hfin_sub : {e ∈ E | r f e}.Finite := hE.subset (fun _ h => h.1)
    have heq : hfin_sub.toFinset = sE.filter (r f) := by
      ext e
      simp [sE, hfin_sub.mem_toFinset, hE.mem_toFinset]
    rw [← heq, ← ncard_eq_toFinset_card _ hfin_sub]
    exact hleft f hfF
  have hR : ∀ e ∈ sE, (∑ f ∈ sF, (if r f e then 1 else 0)) ≤ m := by
    intro e he
    rw [← Finset.card_filter]
    have heE : e ∈ E := hE.mem_toFinset.mp he
    have hfin_sub : {f ∈ F | r f e}.Finite := hF.subset (fun _ h => h.1)
    have heq : hfin_sub.toFinset = sF.filter (fun f => r f e) := by
      ext f
      simp [sF, hfin_sub.mem_toFinset, hF.mem_toFinset]
    rw [← heq, ← ncard_eq_toFinset_card _ hfin_sub]
    exact hright e heE
  rw [hFcard, hEcard]
  calc
    k * sF.card = ∑ _f ∈ sF, k := by simp [Nat.mul_comm]
    _ ≤ ∑ f ∈ sF, ∑ e ∈ sE, (if r f e then 1 else 0) := Finset.sum_le_sum hL
    _ = ∑ e ∈ sE, ∑ f ∈ sF, (if r f e then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ _e ∈ sE, m := Finset.sum_le_sum hR
    _ = m * sE.card := by simp [Nat.mul_comm]

/-- **Euler's bound without triangles.** A plane embedding of a graph with no triangle on a vertex
set `R` with at least three vertices has at most `2 |R| - 4` edges on `R`. -/
theorem triangleFree_edgesOn_ncard_le (φ : PlaneEmbedding G R)
    (htf : ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (h3 : 3 ≤ R.ncard) : (edgesOn G R).ncard ≤ 2 * R.ncard - 4 := by
  have hRne : R.Nonempty := (ncard_pos φ.finite).mp (by omega)
  by_cases hcyc : ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R
  · obtain ⟨C₀, hC₀, hC₀R⟩ := hcyc
    have heuler := φ.euler_ineq _ hRne rfl
    have hfaces : 4 * φ.faces.ncard ≤ 2 * (edgesOn G R).ncard := by
      refine ncard_mul_le_of_rel φ.IsFaceEdge (φ.faces_finite _ rfl) (finite_edgesOn φ.finite) 4 2
        (fun f hf => ?_) (fun e he => φ.ncard_faces_isFaceEdge_le_two he)
      obtain ⟨C, hC, hCR⟩ := φ.exists_cycle_faceGraph hC₀ hC₀R hf
      have htf_f : ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, (φ.faceGraph f).Adj a b →
          (φ.faceGraph f).Adj b c → (φ.faceGraph f).Adj c a → False :=
        fun a ha b hb c hc h₁ h₂ h₃ => htf a ha b hb c hc h₁.2.2.1 h₂.2.2.1 h₃.2.2.1
      rw [← φ.edgesOn_faceGraph_eq f]
      exact (isCycleList_four_le_length_of_noTriangle htf_f hC hCR).trans
        (isCycleList_length_le_edgesOn φ.finite hC hCR)
    omega
  · have hacyc := acyclic_edgesOn_bound (G := G) R.ncard φ.finite rfl hRne hcyc
    omega

end GraphMinor.Wagner
