module

public import GraphMinor.Compute.GM02TerminatedInput
import GraphMinor.Compute.GM02BalancedComplexity

/-!
# Recovering terminated instances from their plain encodings

The bounded base cases in II's recursive algorithm are solved by
exhaustion. To justify a finite decision table on the input words, the
words must determine the graph and all terminal pairs. The graph header
locates the edge prefix and terminal suffix. Flattening endpoint pairs
is injective, and the canonical edge lists determine both graphs.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.GM02 Classical

/-- Flattening numbered endpoint pairs loses no information. -/
theorem gm02FlatEdges_injective {n : ℕ} :
    Function.Injective (flatEdges (n := n)) := by
  intro l
  induction l with
  | nil =>
    intro r h
    cases r with
    | nil => rfl
    | cons p r => simp [flatEdges] at h
  | cons p l ih =>
    intro r h
    cases r with
    | nil => simp [flatEdges] at h
    | cons q r =>
      have he : p.1.val = q.1.val ∧ p.2.val = q.2.val ∧ flatEdges l = flatEdges r := by
        simpa only [flatEdges, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] using h
      have hpq : p = q := Prod.ext (Fin.ext he.1) (Fin.ext he.2.1)
      exact congrArg₂ List.cons hpq (ih he.2.2)

/-- The canonical edge list determines a numbered simple graph. -/
theorem gm02EdgeList_determines_graph {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : edgeListOf G = edgeListOf H) : G = H := by
  ext a b
  rw [(isSimpleEdgeList_edgeListOf G).2.2 a b, (isSimpleEdgeList_edgeListOf H).2.2 a b, h]

/-- The first word is the actual input vertex count. -/
theorem GM02SimpleTerminatedInput.enc_zero (x : GM02SimpleTerminatedInput) :
    x.enc[0]? = some x.n := by simp [GM02SimpleTerminatedInput.enc, encGraph]

/-- The second word is the actual graph edge count. -/
theorem GM02SimpleTerminatedInput.enc_one (x : GM02SimpleTerminatedInput) :
    x.enc[1]? = some (edgeListOf x.G).length := by simp [GM02SimpleTerminatedInput.enc, encGraph]

/-- The edge-count header locates exactly the graph prefix. -/
theorem GM02SimpleTerminatedInput.enc_take_graph (x : GM02SimpleTerminatedInput) :
    x.enc.take (2 + 2 * (edgeListOf x.G).length) = encGraph x.G := by
  have hl := length_encGraph x.G
  rw [← hl]
  simp only [GM02SimpleTerminatedInput.enc, List.append_assoc, List.take_left]

/-- The same header locates exactly the supplied terminal-pair suffix. -/
theorem GM02SimpleTerminatedInput.enc_drop_pairs (x : GM02SimpleTerminatedInput) :
    x.enc.drop (3 + 2 * (edgeListOf x.G).length) = flatEdges (edgeListOf x.A.pairGraph) := by
  have hl : (encGraph x.G ++ [x.A.index]).length = 3 + 2 * (edgeListOf x.G).length := by
    simp only [List.length_append, length_encGraph, List.length_singleton]
    omega
  rw [← hl]
  exact List.drop_left

/-- The plain input words determine the entire numbered terminated instance.
This justifies finite exhaustion on bounded-size encodings in II (3.2). -/
theorem gm02SimpleTerminatedEncoding_injective : Function.Injective GM02SimpleTerminatedInput.enc := by
  intro x y henc
  have hn : x.n = y.n := by
    apply Option.some.inj
    exact x.enc_zero.symm.trans ((congrArg (fun words : List ℕ => words[0]?) henc).trans y.enc_zero)
  rcases x with @⟨n, G, dG, A⟩
  rcases y with @⟨m, H, dH, B⟩
  change n = m at hn
  subst m
  let := dG
  let := dH
  let x : GM02SimpleTerminatedInput := @GM02SimpleTerminatedInput.mk n G dG A
  let y : GM02SimpleTerminatedInput := @GM02SimpleTerminatedInput.mk n H dH B
  change x.enc = y.enc at henc
  have hm : (edgeListOf G).length = (edgeListOf H).length := by
    apply Option.some.inj
    exact x.enc_one.symm.trans ((congrArg (fun words : List ℕ => words[1]?) henc).trans y.enc_one)
  have hprefix : encGraph G = encGraph H := by
    calc
      encGraph G = x.enc.take (2 + 2 * (edgeListOf G).length) := x.enc_take_graph.symm
      _ = y.enc.take (2 + 2 * (edgeListOf G).length) := congrArg (List.take _) henc
      _ = encGraph H := by simpa only [hm] using y.enc_take_graph
  have hflat : flatEdges (edgeListOf G) = flatEdges (edgeListOf H) := by
    have h := congrArg (List.drop 2) hprefix
    simpa [encGraph] using h
  have hG : G = H := gm02EdgeList_determines_graph G H (gm02FlatEdges_injective hflat)
  have hpairs : flatEdges (edgeListOf A.pairGraph) = flatEdges (edgeListOf B.pairGraph) := by
    calc
      flatEdges (edgeListOf A.pairGraph) = x.enc.drop (3 + 2 * (edgeListOf G).length) := x.enc_drop_pairs.symm
      _ = y.enc.drop (3 + 2 * (edgeListOf G).length) := congrArg (List.drop _) henc
      _ = flatEdges (edgeListOf B.pairGraph) := by simpa only [hm] using y.enc_drop_pairs
  have hpairGraph : A.pairGraph = B.pairGraph := gm02EdgeList_determines_graph _ _
    (gm02FlatEdges_injective hpairs)
  have hA : A = B := by
    apply Termination.ext_pairs
    ext p
    induction p using Sym2.inductionOn with
    | hf a b => rw [← A.pairGraph_adj_iff, ← B.pairGraph_adj_iff, hpairGraph]
  cases hG
  cases hA
  have hD : dG = dH := Subsingleton.elim _ _
  cases hD
  rfl

/-- The graph edge count locates the termination-index header. -/
theorem GM02SimpleTerminatedInput.enc_index (x : GM02SimpleTerminatedInput) :
    x.enc[2 + 2 * (edgeListOf x.G).length]? = some x.A.index := by
  have hl := length_encGraph x.G
  rw [← hl]
  simp only [GM02SimpleTerminatedInput.enc, List.append_assoc,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.cons_append, List.nil_append, List.getElem?_cons_zero]

/-- A terminated input cannot be a proper prefix of another input.
The two edge-count headers fix both list lengths. -/
theorem gm02SimpleTerminatedEncoding_prefix_free (x y : GM02SimpleTerminatedInput)
    (rest : List ℕ) (h : x.enc ++ rest = y.enc) : rest = [] := by
  have hxlen := x.enc_length
  have hm : (edgeListOf x.G).length = (edgeListOf y.G).length := by
    apply Option.some.inj
    have he := congrArg (fun words : List ℕ => words[1]?) h
    rw [List.getElem?_append_left (by omega), x.enc_one, y.enc_one] at he
    exact he
  have hi : x.A.index = y.A.index := by
    apply Option.some.inj
    have he := congrArg (fun words : List ℕ => words[2 + 2 * (edgeListOf x.G).length]?) h
    rw [List.getElem?_append_left (by omega), x.enc_index, hm, y.enc_index] at he
    exact he
  have he := congrArg List.length h
  rw [List.length_append, x.enc_length, y.enc_length, hm, hi] at he
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- Fixed vertex bounds give fixed bounds on the length of the plain input. -/
theorem GM02SimpleTerminatedInput.enc_length_le (x : GM02SimpleTerminatedInput)
    {N : ℕ} (hn : x.n ≤ N) : x.enc.length ≤ 3 + 2 * (N * N) + N := by
  have hm := gm02EdgeList_length_le_sq x.G
  have ha := x.support_size_bound
  have hsq := Nat.mul_self_le_mul_self hn
  rw [x.enc_length]
  omega

/-- Each encoded endpoint is a numbered input vertex. -/
private theorem gm02FlatEdges_word_le {n : ℕ} (edges : List (Fin n × Fin n))
    {v : ℕ} (hv : v ∈ flatEdges edges) : v ≤ n := by
  rw [flatEdges, List.mem_flatMap] at hv
  obtain ⟨p, _, hp⟩ := hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact Nat.le_of_lt p.1.isLt
  · exact Nat.le_of_lt p.2.isLt

/-- A fixed vertex bound also bounds every input word, including both headers. -/
theorem GM02SimpleTerminatedInput.enc_word_le (x : GM02SimpleTerminatedInput)
    {N : ℕ} (hn : x.n ≤ N) {v : ℕ} (hv : v ∈ x.enc) : v ≤ N * N + N := by
  have hm := gm02EdgeList_length_le_sq x.G
  have ha := x.support_size_bound
  have hsq := Nat.mul_self_le_mul_self hn
  simp only [GM02SimpleTerminatedInput.enc, encGraph, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (((rfl | rfl) | hv) | rfl) | hv
  · omega
  · omega
  · have he := gm02FlatEdges_word_le (edgeListOf x.G) hv
    omega
  · omega
  · have he := gm02FlatEdges_word_le (edgeListOf x.A.pairGraph) hv
    omega

end GraphMinor.Compute
