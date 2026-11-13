module

public import GraphMinor.Compute.CrossingLiftShrink

/-!
# The graph represented by smaller recorded labels

Shrinking recorded labels changes neither edge incidence nor component membership. The
edge list on the smaller finite type therefore represents the pullback of the original
search graph. Duplicate freedom is also preserved, as required by the graph parser.
-/

public section

namespace GraphMinor.Compute.Crossing

/-- Component membership is preserved by interpreting its labels below the search bound. -/
theorem liftShrinkList_mem {N M : ℕ} (L : List (Fin N)) (h : ∀ x ∈ L, x.val < M)
    (hMN : M ≤ N) (x : Fin M) :
    x ∈ liftShrinkList L h ↔ Fin.castLE hMN x ∈ L := by
  have he := liftShrinkList_cast L h hMN
  constructor
  · intro hx
    rw [← he]
    exact List.mem_map_of_mem hx
  · intro hx
    rw [← he, List.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : y = x := Fin.ext (congrArg (fun v : Fin N => v.val) hyx)
    exact hxy ▸ hy

private theorem pair_cast_injective {N M : ℕ} (hMN : M ≤ N) :
    Function.Injective (fun p : Fin M × Fin M => (Fin.castLE hMN p.1, Fin.castLE hMN p.2)) := by
  intro p q he
  exact Prod.ext (Fin.ext (congrArg (fun p : Fin N × Fin N => p.1.val) he))
    (Fin.ext (congrArg (fun p : Fin N × Fin N => p.2.val) he))

/-- The smaller edge list has exactly the original edges between included vertices. -/
theorem liftShrinkEdges_mem {N M : ℕ} (E : List (Fin N × Fin N))
    (h : ∀ p ∈ E, p.1.val < M ∧ p.2.val < M) (hMN : M ≤ N) (a b : Fin M) :
    (a, b) ∈ liftShrinkEdges E h ↔ (Fin.castLE hMN a, Fin.castLE hMN b) ∈ E := by
  have he := liftShrinkEdges_cast E h hMN
  constructor
  · intro hab
    rw [← he]
    exact List.mem_map_of_mem hab
  · intro hab
    rw [← he, List.mem_map] at hab
    obtain ⟨p, hp, heq⟩ := hab
    exact @pair_cast_injective N M hMN p (a, b) heq ▸ hp

/-- Shrinking cannot introduce repeated edge pairs. -/
theorem liftShrinkEdges_nodup {N M : ℕ} (E : List (Fin N × Fin N))
    (h : ∀ p ∈ E, p.1.val < M ∧ p.2.val < M) (hMN : M ≤ N) (hnd : E.Nodup) :
    (liftShrinkEdges E h).Nodup := by
  apply List.Nodup.of_map (fun p => (Fin.castLE hMN p.1, Fin.castLE hMN p.2))
  rw [liftShrinkEdges_cast]
  exact hnd

/-- A recorded graph is represented on the smaller finite type by its shrunk edges. -/
theorem liftShrinkEdges_adj {N M : ℕ} (G : SimpleGraph (Fin N)) (E : List (Fin N × Fin N))
    (h : ∀ p ∈ E, p.1.val < M ∧ p.2.val < M) (hMN : M ≤ N)
    (hE : ∀ a b, (a, b) ∈ E ↔ G.Adj a b) (a b : Fin M) :
    (a, b) ∈ liftShrinkEdges E h ↔ (G.comap (Fin.castLE hMN)).Adj a b := by
  rw [liftShrinkEdges_mem E h hMN, hE]
  rfl

end GraphMinor.Compute.Crossing
