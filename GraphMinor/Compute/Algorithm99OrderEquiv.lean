module

public import GraphMinor.Compute.Algorithm99OrderTriples
public import GraphMinor.Compute.Algorithm99OrderGroup
import Mathlib.Data.List.GetD

/-!
# The exact edge permutation of the tail sorter

A harmless extra bucket lets the tail key be defined on all natural-number
triples, including when the graph has no vertices. Every real edge has a tail
strictly below the vertex count, so this extra bucket is empty. The stable
bucket positions are exactly the indices of the caller's edge enumeration.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Tail key on arbitrary triples. The last bucket contains no actual edge. -/
def alg99TripleTailKey (n : ℕ) (e : ℕ × ℕ × ℕ) : Fin (n + 1) :=
  ⟨min e.1 n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- The tail keys of the active-pair edge stream. -/
def alg99TailKeys {n : ℕ} (G : MultiDigraph n) : List (Fin (n + 1)) :=
  G.multiEdgeTriples.map (alg99TripleTailKey n)

@[simp]
theorem length_alg99TailKeys {n : ℕ} (G : MultiDigraph n) :
    (alg99TailKeys G).length = G.numEdges := by simp [alg99TailKeys]

/-- Grouping by the total tail key gives the exact lexicographic edge stream. -/
theorem alg99StableGroup_multiEdgeTriples {n : ℕ} (G : MultiDigraph n) :
    alg99StableGroup G.multiEdgeTriples (alg99TripleTailKey n) = G.directedEdgeTriples := by
  have hkey : ∀ e ∈ G.multiEdgeTriples, (alg99TripleTailKey n e).1 = e.1 := by
    intro e he
    have hb := (G.mem_multiEdgeTriples_iff e).1 he
    exact Nat.min_eq_left (Nat.le_of_lt hb.1)
  unfold alg99StableGroup
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  have hrows : (List.finRange n).flatMap (fun u =>
      G.multiEdgeTriples.filter (fun e => decide (alg99TripleTailKey n e = u.castSucc))) =
      G.directedEdgeTriples := by
    rw [← G.group_multiEdgeTriples_tail99]
    apply List.flatMap_congr
    intro u _
    apply List.filter_congr
    intro e he
    have h := hkey e he
    simp only [Fin.ext_iff, Fin.val_castSucc, h]
  rw [hrows]
  have hempty : G.multiEdgeTriples.filter (fun e =>
      decide (alg99TripleTailKey n e = Fin.last n)) = [] := by
    apply List.filter_eq_nil_iff.2
    intro e he
    have hb := (G.mem_multiEdgeTriples_iff e).1 he
    have h := hkey e he
    have hb' : e.1 < n := hb.1
    simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_last, h]
    exact Nat.ne_of_lt hb'
  simp [hempty]

/-- The keys really are the tails of the individual edges in the source order. -/
theorem alg99TailKeys_eq_ofFn {n : ℕ} (G : MultiDigraph n) :
    alg99TailKeys G = List.ofFn (fun i : Fin G.numEdges => (G.edgeEndpoints i).1.castSucc) := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  have hjm : j < G.numEdges := by simpa using hj'
  simp only [alg99TailKeys, List.getElem_map, List.getElem_ofFn]
  apply Fin.ext
  have ht := G.getElem_multiEdgeTriples_fst_snd ⟨j, hjm⟩
  have hfst := congrArg Prod.fst ht
  dsimp only [alg99TripleTailKey, Fin.val_castSucc]
  rw [hfst]
  exact Nat.min_eq_left (Nat.le_of_lt (G.edgeEndpoints ⟨j, hjm⟩).1.2)

/-- The bucket position of the source edge corresponding to a caller edge is
that caller edge's index. In particular, parallel edges are matched separately. -/
theorem alg99BucketPosition_computeToMultiEdgeEquiv {n : ℕ} (G : MultiDigraph n)
    (e : Fin G.toComputeDigraph.numEdges) :
    alg99BucketPosition (alg99TailKeys G)
      ⟨(G.computeToMultiEdgeEquiv e).1, by simp⟩ = e.1 := by
  let i := G.computeToMultiEdgeEquiv e
  have hidx : i.1 < G.multiEdgeTriples.length := by simp
  have hgroup := alg99StableGroup_getD_position G.multiEdgeTriples (alg99TripleTailKey n)
    ⟨i.1, hidx⟩ (0, 0, 0)
  rw [alg99StableGroup_multiEdgeTriples G] at hgroup
  have hpos : alg99BucketPosition (alg99TailKeys G) ⟨i.1, by simp⟩ <
      G.directedEdgeTriples.length := by
    have h := alg99BucketPosition_lt (alg99TailKeys G) ⟨i.1, by simp⟩
    simpa using h
  have he : e.1 < G.directedEdgeTriples.length := by
    simpa [MultiDigraph.toComputeDigraph] using e.2
  have htriple : G.multiEdgeTriples[i.1]'hidx = G.directedEdgeTriples[e.1]'he := by
    have h : G.multiEdgeEquiv i = G.edgeEquiv e := by
      exact G.multiEdgeEquiv.apply_symm_apply (G.edgeEquiv e)
    exact congrArg Subtype.val h
  change G.directedEdgeTriples.getD
    (alg99BucketPosition (alg99TailKeys G) ⟨i.1, by simp⟩) (0, 0, 0) =
      G.multiEdgeTriples[i.1]'hidx at hgroup
  rw [List.getD_eq_getElem _ _ hpos] at hgroup
  have heq := hgroup.trans htriple
  exact (G.nodup_directedEdgeTriples.getElem_inj_iff (hi := hpos) (hj := he)).1 heq

end GraphMinor.Compute
