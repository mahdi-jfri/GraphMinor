module

public import GraphMinor.GM02.Valency
public import GraphMinor.GM02.TopologicalContainment

/-!
# Counts preserved by suppression

Suppression removes two distinct edges and adds one edge, so the edge
count drops by one. At every surviving vertex, the contribution of the
new edge equals the contributions of the two removed edges. This remains
true if their other ends coincide and the new edge is a loop. Thus the
valency of each surviving vertex is unchanged.
-/

public section
namespace GraphMinor.GM02
open Graph Set Finset Classical
open scoped BigOperators
universe u v
variable {α : Type u} {β : Type v} {G : Graph α β}

/-- Suppression decreases the edge count by exactly one. -/
theorem SuppressionData.ncard_edgeSet (d : SuppressionData G) (hE : E(G).Finite) :
    E(d.result).ncard + 1 = E(G).ncard := by
  have hpair : ({d.first, d.second} : Set β) ⊆ E(G) := by
    rintro e (rfl | rfl)
    · exact d.first_link.edge_mem
    · exact d.second_link.edge_mem
  have hpaircard := Set.ncard_pair d.first_ne_second
  have hle := Set.ncard_le_ncard hpair hE
  have hdiff := Set.ncard_sdiff hpair ((Set.finite_singleton d.second).insert d.first)
  have hdis : Disjoint (E(G) \ {d.first, d.second}) {d.fresh} := by
    apply Set.disjoint_left.2
    intro e he hf
    exact d.fresh_notMem (hf ▸ he)
  have hunion := Set.ncard_union_eq hdis hE.sdiff (Set.finite_singleton d.fresh)
  change ((E(G) \ {d.first, d.second}) ∪ {d.fresh}).ncard + 1 = E(G).ncard
  rw [hunion, Set.ncard_singleton, hdiff, hpaircard]
  rw [hpaircard] at hle
  omega

/-- A retained edge contributes the same amount to valency before and
after suppression. -/
theorem SuppressionData.retained_weight_eq (d : SuppressionData G) {e : β}
    (he : e ∈ E(G)) (h1 : e ≠ d.first) (h2 : e ≠ d.second) (x : α) :
    valencyWeight d.result e x = valencyWeight G e x := by
  have hf := d.retained_not_fresh he h1 h2
  have hi : d.result.Inc e x ↔ G.Inc e x := by
    rw [d.inc_iff]
    exact ⟨fun h => h.elim (fun h => (hf h.1).elim) And.left,
      fun h => Or.inr ⟨h, h1, h2⟩⟩
  have hl : d.result.IsLoopAt e x ↔ G.IsLoopAt e x := by
    change d.result.IsLink e x x ↔ G.IsLink e x x
    rw [d.retained_isLink_iff hf]
    exact ⟨And.left, fun h => ⟨h, h1, h2⟩⟩
  simp only [valencyWeight, hi, hl]

/-- At a surviving vertex, the new edge contributes exactly what the two
removed edges contributed. In the loop case both contributions are at the
same surviving vertex. -/
theorem SuppressionData.fresh_weight_eq (d : SuppressionData G) {x : α}
    (hx : x ≠ d.vertex) :
    valencyWeight d.result d.fresh x =
      valencyWeight G d.first x + valencyWeight G d.second x := by
  have hnew : d.result.IsLink d.fresh d.left d.right :=
    Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  rw [valencyWeight_eq_endpoints hnew, valencyWeight_eq_endpoints d.first_link,
    valencyWeight_eq_endpoints d.second_link]
  simp only [hx, ↓reduceIte, Nat.zero_add]

/-- Every surviving vertex keeps its valency under suppression. -/
theorem SuppressionData.valency_eq (d : SuppressionData G) (hE : E(G).Finite)
    {x : α} (hx : x ≠ d.vertex) : valency d.result x = valency G x := by
  let F := hE.toFinset.erase d.first |>.erase d.second
  have hF : ∀ e, e ∈ F ↔ e ∈ E(G) ∧ e ≠ d.first ∧ e ≠ d.second := by
    intro e
    simp only [F, Finset.mem_erase, Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨h.2.2, h.2.1, h.1⟩, fun h => ⟨h.2.2, h.2.1, h.1⟩⟩
  have h1 : d.first ∉ F := fun h => (hF d.first).1 h |>.2.1 rfl
  have h2 : d.second ∉ F := fun h => (hF d.second).1 h |>.2.2 rfl
  have hf : d.fresh ∉ F := by
    intro h
    obtain ⟨he, he1, he2⟩ := (hF d.fresh).1 h
    exact d.fresh_notMem ⟨he, fun h => h.elim he1 he2⟩
  have h1' : d.first ∉ insert d.second F := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · exact d.first_ne_second h
    · exact h1 h
  have hold : hE.toFinset = insert d.first (insert d.second F) := by
    ext e
    rw [Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_insert, hF]
    constructor
    · intro he
      by_cases he1 : e = d.first
      · exact Or.inl he1
      · by_cases he2 : e = d.second
        · exact Or.inr (Or.inl he2)
        · exact Or.inr (Or.inr ⟨he, he1, he2⟩)
    · rintro (rfl | rfl | h)
      · exact d.first_link.edge_mem
      · exact d.second_link.edge_mem
      · exact h.1
  have hE' : E(d.result).Finite := hE.sdiff.union (Set.finite_singleton _)
  have hnew : hE'.toFinset = insert d.fresh F := by
    ext e
    rw [Set.Finite.mem_toFinset, Finset.mem_insert, hF]
    constructor
    · rintro (⟨he, hnot⟩ | h)
      · exact Or.inr ⟨he, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
      · exact Or.inl h
    · rintro (rfl | ⟨he, he1, he2⟩)
      · exact Or.inr rfl
      · exact Or.inl ⟨he, fun h => h.elim he1 he2⟩
  rw [valency_eq_sum d.result hE' x, valency_eq_sum G hE x, hnew, hold,
    Finset.sum_insert hf, Finset.sum_insert h1', Finset.sum_insert h2]
  have hsum : ∑ e ∈ F, valencyWeight d.result e x = ∑ e ∈ F, valencyWeight G e x := by
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨heG, he1, he2⟩ := (hF e).1 he
    exact d.retained_weight_eq heG he1 he2 x
  rw [hsum, d.fresh_weight_eq hx]
  omega

end GraphMinor.GM02
