module

public import GraphMinor.Minor.Model
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Valency for the multigraph patterns in Graph Minors II

The valency used in II (4.8), page 320, counts each non-loop incident
edge once and each loop twice. Express it as the number of incident
edges plus the number of incident loops. For a finite edge set this is
a sum of edge contributions. Each contribution is the sum of the two
endpoint indicators, with repeated endpoints counted twice.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
open scoped BigOperators
universe u v

/-- The edges incident with a vertex. -/
def incidentEdges {α : Type u} {β : Type v} (G : Graph α β) (x : α) : Set β :=
  {e | G.Inc e x}

/-- The loops incident with a vertex. -/
def loopEdges {α : Type u} {β : Type v} (G : Graph α β) (x : α) : Set β :=
  {e | G.IsLoopAt e x}

/-- Valency, as used in Graph Minors II, (4.8), page 320. A loop has two
ends at the same vertex, so it contributes twice. -/
noncomputable def valency {α : Type u} {β : Type v} (G : Graph α β) (x : α) : ℕ :=
  (incidentEdges G x).ncard + (loopEdges G x).ncard

/-- The contribution of an edge to a vertex's valency. -/
noncomputable def valencyWeight {α : Type u} {β : Type v}
    (G : Graph α β) (e : β) (x : α) : ℕ :=
  (if G.Inc e x then 1 else 0) + (if G.IsLoopAt e x then 1 else 0)

/-- Incident-edge sets in a finite graph are finite. -/
theorem incidentEdges_finite {α : Type u} {β : Type v} {G : Graph α β}
    (hE : E(G).Finite) (x : α) : (incidentEdges G x).Finite :=
  hE.subset (fun _ h => h.edge_mem)

/-- Loop-edge sets in a finite graph are finite. -/
theorem loopEdges_finite {α : Type u} {β : Type v} {G : Graph α β}
    (hE : E(G).Finite) (x : α) : (loopEdges G x).Finite :=
  hE.subset (fun _ h => h.edge_mem)

/-- Valency is the sum of the contributions of the finite edge set. -/
theorem valency_eq_sum {α : Type u} {β : Type v} (G : Graph α β)
    (hE : E(G).Finite) (x : α) :
    valency G x = ∑ e ∈ hE.toFinset, valencyWeight G e x := by
  have hI : (incidentEdges G x).ncard =
      ∑ e ∈ hE.toFinset, if G.Inc e x then 1 else 0 := by
    have heq : (↑(hE.toFinset.filter (fun e => G.Inc e x)) : Set β) = incidentEdges G x := by
      ext e
      simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨And.right, fun h => ⟨h.edge_mem, h⟩⟩
    rw [← heq, Set.ncard_coe_finset]
    simp only [Finset.sum_boole, Nat.cast_id]
  have hL : (loopEdges G x).ncard =
      ∑ e ∈ hE.toFinset, if G.IsLoopAt e x then 1 else 0 := by
    have heq : (↑(hE.toFinset.filter (fun e => G.IsLoopAt e x)) : Set β) = loopEdges G x := by
      ext e
      simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨And.right, fun h => ⟨h.edge_mem, h⟩⟩
    rw [← heq, Set.ncard_coe_finset]
    simp only [Finset.sum_boole, Nat.cast_id]
  exact (congrArg₂ Nat.add hI hL).trans (Finset.sum_add_distrib.symm)

/-- The contribution of one edge is its two endpoint indicators. This
formula treats a loop by counting the repeated endpoint twice. -/
theorem valencyWeight_eq_endpoints {α : Type u} {β : Type v}
    {G : Graph α β} {e : β} {a b : α} (hab : G.IsLink e a b) (x : α) :
    valencyWeight G e x = (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  have hinc : G.Inc e x ↔ x = a ∨ x = b := by
    constructor
    · exact fun hx => hx.eq_or_eq_of_isLink hab
    · rintro (rfl | rfl)
      · exact hab.inc_left
      · exact hab.inc_right
  have hloop : G.IsLoopAt e x ↔ x = a ∧ a = b := by
    constructor
    · intro hx
      exact ⟨(hx.eq_of_inc hab.inc_left),
        (hx.eq_of_inc hab.inc_left).symm.trans (hx.eq_of_inc hab.inc_right)⟩
    · rintro ⟨rfl, rfl⟩
      exact hab
  unfold valencyWeight
  rw [hinc, hloop]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all

/-- The sum of all valencies of a finite multigraph is twice its edge
count. Each edge contributes its two endpoint indicators, even for loops. -/
theorem sum_valency {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    ∑ x ∈ hV.toFinset, valency G x = 2 * E(G).ncard := by
  have hedge : ∀ e ∈ hE.toFinset, ∑ x ∈ hV.toFinset, valencyWeight G e x = 2 := by
    intro e he
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet ((hE.mem_toFinset).1 he)
    simp_rw [valencyWeight_eq_endpoints hab]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', hV.mem_toFinset, hab.left_mem, hab.right_mem, ↓reduceIte]
  calc
    _ = ∑ x ∈ hV.toFinset, ∑ e ∈ hE.toFinset, valencyWeight G e x :=
      Finset.sum_congr rfl (fun x _ => valency_eq_sum G hE x)
    _ = ∑ e ∈ hE.toFinset, ∑ x ∈ hV.toFinset, valencyWeight G e x := Finset.sum_comm
    _ = ∑ _e ∈ hE.toFinset, 2 := Finset.sum_congr rfl hedge
    _ = 2 * E(G).ncard := by
      rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card E(G) hE]
      exact Nat.mul_comm _ _

end GraphMinor.GM02
