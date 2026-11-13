module

public import GraphMinor.GM21.Section6Jumps
import GraphMinor.GM21.LinkagePaths

/-!
# Graph Minors XXI, (6.3), claim (3): walking along a jump

Claim (3) of the proof of (6.3) (page 29 of the preprint) says: "If $c(\Sigma) \ge 2$ then
there is a region of $\Gamma$ incident with vertices in two different cuffs". To find these vertices
we walk along a jump of `Γ` inside the closure of a region. The walk passes only through vertices
outside `bd(Σ)`, and at such a vertex both edges of `Γ` belong to the jump. This file proves the
graph part of the walk (`vertexSet_subset_of_propagate`).

Let `J` be a jump: a path with its two ends in `B` and no other vertex in `B`. Let `Z` be a set of
vertices and `ZE` a set of edges such that
* both ends of an edge of `J` in `ZE` are in `Z`, and
* every edge of `J` at a vertex of `Z` outside `B` is in `ZE`.
If `ZE` holds an edge of `J`, or `Z` holds a vertex of `J` outside `B`, then `Z` holds every vertex of
`J`. We number the vertices of `J` as `v 0, …, v m` along the path. Only `v 0` and `v m` lie in `B`,
so from a vertex `v i ∈ Z` with `0 < i < m` we may step to `v (i - 1)` and to `v (i + 1)`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ClaimThree

open Set Function Hypergraph

universe u v

variable {α : Type u} {β : Type v} {K J : Hypergraph α β} {B : Set α}

/-- **Walking along a jump.** If `ZE` holds an edge of the jump `J`, or `Z` holds a vertex of `J`
outside `B`, and the walk can go on from each vertex of `Z` outside `B` (`hb`) and along each edge
of `ZE` (`ha`), then `Z` holds every vertex of `J`. -/
theorem vertexSet_subset_of_propagate (hJ : J ∈ jumpSet K B) {Z : Set α} {ZE : Set β}
    (ha : ∀ f ∈ J.edgeSet, f ∈ ZE → ∀ x, J.Inc f x → x ∈ Z)
    (hb : ∀ x ∈ J.vertexSet, x ∈ Z → x ∉ B → ∀ f ∈ J.edgeSet, J.Inc f x → f ∈ ZE)
    (hstart : (∃ f ∈ J.edgeSet, f ∈ ZE) ∨ ∃ x ∈ J.vertexSet, x ∈ Z ∧ x ∉ B) :
    J.vertexSet ⊆ Z := by
  have hJp : IsPathGraph J := hJ.2.1
  obtain ⟨x₁, -, x₂, -, -, ⟨m, hm, w, hinj, h0, hmw, hV, hadj⟩, hdeg1⟩ :=
    exists_isIndexedPath_of_isPathGraph hJp (edgeSet_nonempty_of_mem_jumpSet hJ)
  have hwV : ∀ i, w i ∈ J.vertexSet := fun i => hV ▸ mem_range_self i
  -- The two ends of the path lie in `B`, and no other vertex does.
  have hendB : ∀ x ∈ J.vertexSet, (x = x₁ ∨ x = x₂) → x ∈ B := fun x hx h =>
    terminals_subset_of_mem_jumpSet hJ
      ⟨hx, by rw [vertexDegree_eq_ncard_incidentEdges hJp.2.2.2.1]; exact (hdeg1 x hx).2 h⟩
  have hinB : ∀ i : Fin (m + 1), w i ∈ B → i.1 = 0 ∨ i.1 = m := by
    intro i hi
    have ht := mem_terminals_of_mem_jumpSet hJ (hwV i) hi
    have h1 : (incidentEdges J (w i)).ncard ≤ 1 := by
      have := ht.2
      rwa [vertexDegree_eq_ncard_incidentEdges hJp.2.2.2.1] at this
    rcases (hdeg1 (w i) (hwV i)).1 h1 with h | h
    · left
      have := hinj (h.trans h0.symm)
      exact congrArg Fin.val this
    · right
      have := hinj (h.trans hmw.symm)
      exact congrArg Fin.val this
  -- An edge of `J` between two consecutive vertices.
  have hedge : ∀ i k : Fin (m + 1), i.1 + 1 = k.1 →
      ∃ f ∈ J.edgeSet, J.Inc f (w i) ∧ J.Inc f (w k) := by
    intro i k hik
    obtain ⟨-, f, hfi, hfk⟩ := (hadj i k).2 (Or.inl hik)
    exact ⟨f, J.edge_mem_of_inc hfi, hfi, hfk⟩
  let Q : ℕ → Prop := fun n => ∀ h : n < m + 1, w ⟨n, h⟩ ∈ Z
  -- One step from an inside vertex of `Z`.
  have hstep : ∀ n, 0 < n → n < m → Q n → Q (n + 1) ∧ Q (n - 1) := by
    intro n hn0 hnm hQ
    have hn : w ⟨n, by omega⟩ ∉ B := fun h => by
      rcases hinB _ h with h' | h' <;> simp at h' <;> omega
    have hZ := hQ (by omega)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨f, hf, hfi, hfk⟩ := hedge ⟨n, by omega⟩ ⟨n + 1, h⟩ rfl
      exact ha f hf (hb _ (hwV _) hZ hn f hf hfi) _ hfk
    · obtain ⟨f, hf, hfi, hfk⟩ := hedge ⟨n - 1, h⟩ ⟨n, by omega⟩ (by simp; omega)
      exact ha f hf (hb _ (hwV _) hZ hn f hf hfk) _ hfi
  have hup : ∀ a, 0 < a → Q a → ∀ k, a + k ≤ m → Q (a + k) := by
    intro a ha0 hQa k
    induction k with
    | zero => exact fun _ => hQa
    | succ k ih =>
      intro hk
      exact (hstep (a + k) (by omega) (by omega) (ih (by omega))).1
  have hdown : ∀ b, b < m → Q b → ∀ k, k ≤ b → Q (b - k) := by
    intro b hbm hQb k
    induction k with
    | zero => exact fun _ => hQb
    | succ k ih =>
      intro hk
      have := (hstep (b - k) (by omega) (by omega) (ih (by omega))).2
      rwa [show b - k - 1 = b - (k + 1) by omega] at this
  -- Two starting places `a ≤ b + 1` with `0 < a` and `b < m`.
  obtain ⟨a, b, ha0, hbm, hab, hQa, hQb⟩ : ∃ a b, 0 < a ∧ b < m ∧ a ≤ b + 1 ∧ Q a ∧ Q b := by
    rcases hstart with ⟨f, hf, hfZ⟩ | ⟨x, hx, hxZ, hxB⟩
    · obtain ⟨y₁, y₂, hy, hends⟩ := ncard_eq_two.mp (hJp.2.2.2.1 f hf)
      have hy₁ : J.Inc f y₁ := by
        have : y₁ ∈ J.ends f := hends ▸ Or.inl rfl
        exact this
      have hy₂ : J.Inc f y₂ := by
        have : y₂ ∈ J.ends f := hends ▸ Or.inr rfl
        exact this
      obtain ⟨i, rfl⟩ : y₁ ∈ range w := hV ▸ J.vertex_mem_of_inc hy₁
      obtain ⟨k, rfl⟩ : y₂ ∈ range w := hV ▸ J.vertex_mem_of_inc hy₂
      have hQi : Q i.1 := fun h => ha f hf hfZ _ hy₁
      have hQk : Q k.1 := fun h => ha f hf hfZ _ hy₂
      have hik : i.1 + 1 = k.1 ∨ k.1 + 1 = i.1 := (hadj i k).1 ⟨hy, f, hy₁, hy₂⟩
      rcases hik with h | h
      · exact ⟨k.1, i.1, by omega, by omega, by omega, hQk, hQi⟩
      · exact ⟨i.1, k.1, by omega, by omega, by omega, hQi, hQk⟩
    · obtain ⟨i, rfl⟩ : x ∈ range w := hV ▸ hx
      have hi0 : i.1 ≠ 0 := fun h => hxB (hendB _ hx (Or.inl (by
        rw [← h0]; exact congrArg w (Fin.ext h))))
      have him : i.1 ≠ m := fun h => hxB (hendB _ hx (Or.inr (by
        rw [← hmw]; exact congrArg w (Fin.ext h))))
      have hQi : Q i.1 := fun h => hxZ
      exact ⟨i.1, i.1, by omega, by omega, by omega, hQi, hQi⟩
  rw [hV]
  rintro _ ⟨i, rfl⟩
  have hi := i.2
  by_cases hia : a ≤ i.1
  · have := hup a ha0 hQa (i.1 - a) (by omega)
    rw [show a + (i.1 - a) = i.1 by omega] at this
    exact this i.2
  · have := hdown b hbm hQb (b - i.1) (by omega)
    rw [show b - (b - i.1) = i.1 by omega] at this
    exact this i.2

end ClaimThree
end GM21
end GraphMinor
