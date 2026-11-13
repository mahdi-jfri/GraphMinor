module

public import GraphMinor.Compute.GM02CompactEdges
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Rewriting surviving edge words by compact vertex ranks

The edge filter leaves a two-word header followed by surviving endpoints.
Read each endpoint, look up its compact rank, and write the ranks to a
fresh array. The loop is linear in the edge-list length and keeps the
source, rank table, and all other registers except its counter.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Rewrite the endpoint words after a two-word header, using edge count
register 22 and loop counter 250. -/
def gm02RankEdgeWordsProg (src rank dst : Arr) : Cmd :=
  gm13TabulateProg 250 (.op .mul (.const 2) (.reg 22))
    (.read rank (.read src (.op .add (.const 2) (.reg 250)))) dst

/-- The rank-substitution loop writes exactly the mapped endpoint words. -/
theorem gm02RankEdgeWordsProg_exec {n w : ℕ} (Z : Finset (Fin n))
    (edges : List (Fin n × Fin n)) (src rank dst : Arr) (hsd : src ≠ dst) (hrd : rank ≠ dst)
    (header₀ header₁ : ℕ) (rest : List ℕ) (s : State) (hn : n < 2 ^ w)
    (hlen : 2 + 2 * edges.length < 2 ^ w)
    (hsrc : s.arrs src = [header₀, header₁] ++ flatEdges edges ++ rest)
    (hrank : s.arrs rank = List.ofFn (fun v : Fin n => compactRank Z v.val))
    (hm : s.regs 22 = edges.length) :
    ∃ s' t, Exec w (gm02RankEdgeWordsProg src rank dst) s s' t ∧
      t ≤ 10 + 38 * edges.length ∧ Keeps [250] [dst] s s' ∧
      s'.arrs dst = (flatEdges edges).map (compactRank Z) := by
  let words := flatEdges edges
  have hl : words.length = 2 * edges.length := length_flatEdges edges
  have htwo : 2 < 2 ^ w := by omega
  rcases gm13TabulateProg_exec (w := w) 250
    (.op .mul (.const 2) (.reg 22))
    (.read rank (.read src (.op .add (.const 2) (.reg 250)))) dst
    (words.map (compactRank Z)) s (by omega) (by simp only [List.length_map, hl]; omega)
    (fun st hk => by
      rw [List.length_map, hl]
      exact eval_mul (eval_const htwo)
        (eval_reg ((hk.1 _ (by decide)).trans hm) (by omega)) (by omega))
    (fun st i hi hk hri => by
      have hiw : i < words.length := by simpa only [List.length_map] using hi
      have hiv : words[i] < n := by
        have hv : words[i] ∈ flatEdges edges := List.getElem_mem hiw
        rw [flatEdges, List.mem_flatMap] at hv
        obtain ⟨p, _, hp⟩ := hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with hp | hp
        · exact hp ▸ p.1.isLt
        · exact hp ▸ p.2.isLt
      have hsa : st.arrs src = [header₀, header₁] ++ words ++ rest :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hsd)).trans hsrc
      have hra : st.arrs rank = List.ofFn (fun v : Fin n => compactRank Z v.val) :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hrd)).trans hrank
      have his : 2 + i < (st.arrs src).length := by
        simp only [hsa, List.length_append, List.length_cons, List.length_nil]
        omega
      have hiapp : i < (words ++ rest).length := by rw [List.length_append]; omega
      have hget : (st.arrs src)[2 + i] = words[i] := by
        simpa only [hsa, List.cons_append, List.nil_append, Nat.add_comm 2 i,
          List.getElem_cons_succ] using (List.getElem_append_left hiw : (words ++ rest)[i] = words[i])
      have hir : words[i] < (st.arrs rank).length := by simpa only [hra, List.length_ofFn] using hiv
      have hgetr : (st.arrs rank)[words[i]] = compactRank Z words[i] := by
        simp only [hra, List.getElem_ofFn]
      have heidx := eval_add (eval_const htwo) (eval_reg hri (by omega : i < 2 ^ w))
        (by omega : 2 + i < 2 ^ w)
      have hesrc := eval_read (a := src) heidx his (by rw [hget]; exact hiv.trans hn)
      rw [hget] at hesrc
      have herank := eval_read (a := rank) hesrc hir (by
        rw [hgetr]
        exact (compactRank_le Z _).trans_lt hn)
      simpa only [List.getElem_map, hgetr] using herank) with
    ⟨s', t, he, ht, hk, hout⟩
  refine ⟨s', t, he, ?_, hk, hout⟩
  simp only [Expr.cost_op, Expr.cost_const, Expr.cost_reg, Expr.cost_read,
    List.length_map, hl] at ht
  omega

end GraphMinor.Compute
