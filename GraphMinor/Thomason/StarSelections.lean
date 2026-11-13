module

public import GraphMinor.Thomason.SubsetMissingCount
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Connected selections with a centre inside the selection

Choose a vertex and some of its neighbours. The resulting set is already
connected. Counting these choices by their centre and then by their
endpoint set gives a lower bound on the number of connected candidates.
Each candidate can have at most as many centres as it has vertices.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A possible centre of a vertex set is joined to every other vertex in it. -/
def isSelectionCentre (Y : Finset V) (v : V) : Prop :=
  v ∈ Y ∧ ∀ w ∈ Y, w ≠ v → G.Adj v w

instance (Y : Finset V) (v : V) : Decidable (isSelectionCentre G Y v) := by
  unfold isSelectionCentre
  infer_instance

/-- Selections of `k` vertices that contain a centre. -/
def starSelections (k : ℕ) : Finset (Finset V) :=
  (univ : Finset V).powersetCard k |>.filter (fun Y => ∃ v, isSelectionCentre G Y v)

/-- Star selections are `k`-element subsets. -/
theorem starSelections_subset_powersetCard (k : ℕ) :
    starSelections G k ⊆ (univ : Finset V).powersetCard k := filter_subset _ _

/-- A centre joins every pair of vertices by a path of length at most two. -/
theorem connected_of_mem_starSelections (k : ℕ) (Y : Finset V)
    (hY : Y ∈ starSelections G k) : (G.induce (Y : Set V)).Connected := by
  obtain ⟨_, v, hv, hAdj⟩ := mem_filter.mp hY
  have hreach (w : Y) : (G.induce (Y : Set V)).Reachable ⟨v, hv⟩ w := by
    by_cases hw : w.val = v
    · have heq : w = ⟨v, hv⟩ := Subtype.ext hw
      subst w
      exact .rfl
    · exact (show (G.induce (Y : Set V)).Adj ⟨v, hv⟩ w from hAdj w.val w.property hw).reachable
  let : Nonempty Y := ⟨⟨v, hv⟩⟩
  exact ⟨fun a b => (hreach a).symm.trans (hreach b)⟩

/-- Every choice of neighbours produces a distinct selection centred at
its specified vertex. -/
theorem choose_degree_le_card_centred_selections (k : ℕ) (hk : 0 < k) (v : V) :
    (G.degree v).choose (k - 1) ≤
      ((starSelections G k).bipartiteBelow (isSelectionCentre G) v).card := by
  let S := (G.neighborFinset v).powersetCard (k - 1)
  have hvnot (A : Finset V) (hA : A ∈ S) : v ∉ A := by
    intro hv
    have hh := (mem_powersetCard.mp hA).1 hv
    exact G.irrefl ((G.mem_neighborFinset v v).mp hh)
  have hinj : Set.InjOn (fun A : Finset V => insert v A) S := by
    intro A hA B hB hab
    have heq := congrArg (fun A : Finset V => A.erase v) hab
    rw [erase_insert (hvnot A hA), erase_insert (hvnot B hB)] at heq
    exact heq
  have hsub : S.image (insert v) ⊆
      (starSelections G k).bipartiteBelow (isSelectionCentre G) v := by
    intro Y hY
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hY
    have hcentre : isSelectionCentre G (insert v A) v := by
      refine ⟨mem_insert_self _ _, ?_⟩
      intro w hw hne
      have hwA : w ∈ A := (mem_insert.mp hw).resolve_left hne
      exact (G.mem_neighborFinset v w).mp ((mem_powersetCard.mp hA).1 hwA)
    apply (mem_bipartiteBelow _).mpr
    refine ⟨mem_filter.mpr ⟨?_, ⟨v, hcentre⟩⟩, hcentre⟩
    apply mem_powersetCard.mpr
    refine ⟨subset_univ _, ?_⟩
    rw [card_insert_of_notMem (hvnot A hA), (mem_powersetCard.mp hA).2]
    omega
  have hc := (card_le_card hsub)
  rw [card_image_of_injOn hinj] at hc
  simpa only [S, card_powersetCard, G.card_neighborFinset_eq_degree] using hc

/-- Counting centres in two orders gives a lower bound on the number of
star selections from any minimum-degree bound. -/
theorem card_starSelections_lower (k r : ℕ) (hk : 0 < k)
    (hdegree : ∀ v, r ≤ G.degree v) :
    Fintype.card V * r.choose (k - 1) ≤ k * (starSelections G k).card := by
  have hrow (Y : Finset V) (hY : Y ∈ starSelections G k) :
      ((univ : Finset V).bipartiteAbove (isSelectionCentre G) Y).card ≤ k := by
    have hsub : (univ : Finset V).bipartiteAbove (isSelectionCentre G) Y ⊆ Y := by
      intro v hv
      exact ((mem_bipartiteAbove _).mp hv).2.1
    exact (card_le_card hsub).trans_eq
      (mem_powersetCard.mp (starSelections_subset_powersetCard G k hY)).2
  have hcount := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (isSelectionCentre G)
    (s := starSelections G k) (t := univ)
  calc
    Fintype.card V * r.choose (k - 1) = ∑ _v : V, r.choose (k - 1) := by simp
    _ ≤ ∑ v : V, ((starSelections G k).bipartiteBelow (isSelectionCentre G) v).card := by
      apply sum_le_sum
      intro v _
      exact (Nat.choose_le_choose _ (hdegree v)).trans
        (choose_degree_le_card_centred_selections G k hk v)
    _ = ∑ Y ∈ starSelections G k, ((univ : Finset V).bipartiteAbove (isSelectionCentre G) Y).card := hcount.symm
    _ ≤ ∑ _Y ∈ starSelections G k, k := sum_le_sum hrow
    _ = k * (starSelections G k).card := by simp [Nat.mul_comm]

end GraphMinor.Thomason
