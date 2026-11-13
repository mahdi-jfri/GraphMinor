module

public import GraphMinor.Compute.GM02LookupTemplateWords
public import GraphMinor.Compute.GM02CompactTermination
public import GraphMinor.Compute.GM02TerminalVertices

/-!
# Rewriting a child matching array by compact ranks

Every prescribed endpoint survives in the child vertex set. Its
canonical matching words can therefore be rewritten through the same
rank array as the graph edges. This produces exactly the compact
termination suffix, with no extra filtering or endpoint certificate.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02 GraphMinor.Compute.Crossing TwoPaths

/-- The rank of any parent vertex is a valid parent-sized word index. -/
def gm02RankVertex {n : ℕ} (Z : Finset (Fin n)) (v : Fin n) : Fin n :=
  ⟨compactRank Z v.val, by
    have hs : ((Finset.univ : Finset (Fin n)).filter
        (fun u => u ∉ Z ∧ u.val < v.val)) ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro he
      have hv := he.symm ▸ Finset.mem_univ v
      exact Nat.lt_irrefl v.val (Finset.mem_filter.mp hv).2.2
    simpa only [compactRank, Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hs⟩

/-- Rank lookup on a canonical matching array writes the exact compact suffix. -/
theorem gm02RankPairArray_exec {n w : ℕ} (Z : Finset (Fin n))
    (A : Termination {v : Fin n | v ∉ Z}) (src rank dst : Arr)
    (hsd : src ≠ dst) (hrd : rank ≠ dst) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlen : 2 * A.index < 2 ^ w)
    (hsrc : s.arrs src = flatEdges (edgeListOf A.pairGraph))
    (hrank : s.arrs rank = List.ofFn (fun v : Fin n => compactRank Z v.val)) :
    ∃ s' t, Exec w (gm02LookupTemplateWordsProg src rank dst) s s' t ∧
      t ≤ 6 + 30 * A.index ∧ Keeps [342] [dst] s s' ∧
      s'.arrs dst = flatEdges (edgeListOf (gm02CompactTermination Z A).pairGraph) := by
  let A₀ := A.rebase (Set.subset_univ A.support)
  let indices := gm02TerminalVertices A₀
  have hl : indices.length = 2 * A.index := by
    exact (gm02TerminalVertices_length A₀).trans (congrArg (2 * ·) (A.rebase_index _))
  have hs : s.arrs src = indices.map Fin.val := by
    simp only [indices, A₀, gm02TerminalVertices_map_val, Termination.rebase_pairGraph]
    convert hsrc using 1; rfl
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm02LookupTemplateWordsProg_exec
    (gm02RankVertex Z) indices src rank dst hsd hrd s hw hn hn (by omega) hs hrank
  refine ⟨s', t, he, ?_, hk, ?_⟩
  · rw [hl] at ht
    omega
  · rw [gm02CompactTermination_pairWords]
    rw [hout]
    change (gm02TerminalVertices A₀).map (fun i => compactRank Z i.val) = _
    have heq := congrArg (List.map (compactRank Z)) (gm02TerminalVertices_map_val A₀)
    simp only [List.map_map, Function.comp_def, A₀, Termination.rebase_pairGraph] at heq
    convert heq using 1; rfl

end GraphMinor.Compute
