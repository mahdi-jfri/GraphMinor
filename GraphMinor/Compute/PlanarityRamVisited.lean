module

public import GraphMinor.Compute.PlanarityRamBackEdge
public import GraphMinor.Compute.PlanarityRamBoundedFinish
import GraphMinor.Compute.PlanarityRamBoundedDiscover

/-!
# Deciding the visited-neighbor branch

For a discovered neighbor, the program first skips the reverse parent
incidence. It then compares the two tagged depths and creates a back edge
only when the neighbor is shallower. Tags preserve this comparison because
both depths are present. The proof follows these two tests in order.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Comparing a tagged optional label with a present label is exact. -/
theorem optionWord_eq_some (parent : Option ℕ) (u : ℕ) :
    optionWord parent = u + 1 ↔ parent = some u := by
  cases parent <;> simp [optionWord]

/-- A stored optional parent label has tag at most N. -/
theorem SearchBounded.parent_tag_le {N : ℕ} {search : Search} (h : SearchBounded N search)
    (v : Fin N) : optionWord (search.parent[v.val]?.join) ≤ N := by
  cases hp : search.parent[v.val]?.join with
  | none => simp [optionWord]
  | some p =>
    have hh := h.2.2.2.2.1 v p hp
    simp only [optionWord]
    omega

/-- The state selected for an already discovered neighbor. -/
def visitedSearch (search : Search) (v u : ℕ) : Search :=
  if search.parent[v]?.join ≠ some u ∧
      (search.depth[u]?.join).getD 0 < (search.depth[v]?.join).getD 0 then
    finishEdge (addEdge search v u false).1 search.edges.size
  else search

private theorem eq_expr_eval {w : ℕ} {s : State} {A B : Expr} {a b : ℕ}
    (ha : A.eval w s = some a) (hb : B.eval w s = some b) (hw : 1 < 2 ^ w) :
    (Expr.op .eq A B).eval w s = some (decide (a = b)).toNat := by
  rw [Expr.eval, ha, hb]
  simp only [BinOp.eval, BinOp.raw]
  by_cases he : a = b <;> simp [he, checkWord_of_lt, hw]

private theorem lt_expr_eval {w : ℕ} {s : State} {A B : Expr} {a b : ℕ}
    (ha : A.eval w s = some a) (hb : B.eval w s = some b) (hw : 1 < 2 ^ w) :
    (Expr.op .lt A B).eval w s = some (decide (a < b)).toNat := by
  rw [Expr.eval, ha, hb]
  simp only [BinOp.eval, BinOp.raw]
  by_cases he : a < b <;> simp [he, checkWord_of_lt, hw]

/-- Both visited-neighbor tests and the possible back-edge call take at
most 125 steps. The source and target depths are present, endpoints are
valid and loaded, and a record slot is available when the tests accept. -/
theorem visitedNeighborProg_refines {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} (h : DfsSearchAt N M s search) (hf : FramesAt N s stack)
    (hb : SearchBounded N search) (v u dv du : ℕ) (hv : v < N) (hu : u < N)
    (hdv : search.depth[v]?.join = some dv) (hdu : search.depth[u]?.join = some du)
    (hrv : s.regs 41 = v) (hru : s.regs 43 = u) (hfree : search.edges.size < M)
    (hw : 2 * (N + M + 2) < 2 ^ w) :
    ∃ s' t, Exec w visitedNeighborProg s s' t ∧ t ≤ 125 ∧ FramesAt N s' stack ∧
      DfsSearchAt N M s' (visitedSearch search v u) := by
  have hvp : v < search.parent.size := by rw [hb.2.1]; exact hv
  have hvd : v < search.depth.size := by rw [hb.1]; exact hv
  have hud : u < search.depth.size := by rw [hb.1]; exact hu
  have hdvN := hb.2.2.2.1 ⟨v, hv⟩ dv hdv
  have hduN := hb.2.2.2.1 ⟨u, hu⟩ du hdu
  have hparentTag : optionWord (search.parent[v]?.join) ≤ N := hb.parent_tag_le ⟨v, hv⟩
  have pPrefix : PrefixAt s Field.parent.array N (search.parent.toList.map optionWord) := h.2.2.2.2.2.2.1
  have dPrefix : PrefixAt s Field.depth.array N (search.depth.toList.map optionWord) := h.2.2.2.2.2.1
  have hrawP : search.parent[v] = search.parent[v]?.join := by
    simp [Array.getElem?_eq_getElem hvp]
  have hrawV : search.depth[v] = some dv := by
    simpa only [Array.getElem?_eq_getElem hvd, Option.join_some] using hdv
  have hrawU : search.depth[u] = some du := by
    simpa only [Array.getElem?_eq_getElem hud, Option.join_some] using hdu
  have hvw : v < 2 ^ w := by omega
  have huw : u < 2 ^ w := by omega
  have huwTag : u + 1 < 2 ^ w := by omega
  have hdvTag : dv + 1 < 2 ^ w := by omega
  have hduTag : du + 1 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have ep : (Expr.read Field.parent.array (.reg 41)).eval w s =
      some (optionWord (search.parent[v]?.join)) := by
    have hh := pPrefix.read_option_reg hvp hrv hvw
      (by rw [hrawP]; omega)
    simpa only [hrawP] using hh
  have ev : (Expr.read Field.depth.array (.reg 41)).eval w s = some (dv + 1) := by
    have hh := dPrefix.read_option_reg hvd hrv hvw
      (by simpa only [hrawV, optionWord] using hdvTag)
    simpa only [hrawV, optionWord] using hh
  have eu : (Expr.read Field.depth.array (.reg 43)).eval w s = some (du + 1) := by
    have hh := dPrefix.read_option_reg hud hru huw
      (by simpa only [hrawU, optionWord] using hduTag)
    simpa only [hrawU, optionWord] using hh
  have eutag : (Expr.op .add (.reg 43) (.const 1)).eval w s = some (u + 1) := by
    simp [Expr.eval, hru, BinOp.eval, BinOp.raw, checkWord_of_lt huw,
      checkWord_of_lt hone, checkWord_of_lt huwTag]
  have eparent := eq_expr_eval ep eutag hone
  have edepth := lt_expr_eval eu ev hone
  by_cases hp : search.parent[v]?.join = some u
  · have hpt : optionWord (search.parent[v]?.join) = u + 1 := (optionWord_eq_some _ _).mpr hp
    simp only [hpt, decide_true, Bool.toNat_true] at eparent
    refine ⟨s, 7, Exec.ite_true eparent (by decide) (Exec.skip s), by omega, hf, ?_⟩
    simpa [visitedSearch, hp] using h
  · have hpt : ¬optionWord (search.parent[v]?.join) = u + 1 := by
      intro hh
      exact hp ((optionWord_eq_some _ _).mp hh)
    simp only [hpt, decide_false, Bool.toNat_false] at eparent
    by_cases hlt : du < dv
    · have hltTag : du + 1 < dv + 1 := by omega
      simp only [hltTag, decide_true, Bool.toNat_true] at edepth
      have hadded := hb.addEdge v u hv hu false
      have hlast : search.edges.size < (addEdge search v u false).1.edges.size := by simp [addEdge]
      have hkeyN := hadded.finishedKey_le search.edges.size hlast
      have hparent : ∀ p : ℕ, search.parentEdge[v]?.join = some p →
          p < search.edges.size ∧ p + 1 < 2 ^ w ∧
          search.edges[p]!.pair.low < 2 ^ w ∧ search.edges[p]!.pair.second < 2 ^ w := by
        intro p hp'
        have hpi := hb.2.2.2.2.2.1 ⟨v, hv⟩ p hp'
        have he := hb.2.2.2.2.2.2 p hpi
        have hl : search.edges[p]!.pair.low < N := he.2.2.1
        have hh : search.edges[p]!.pair.second < N := he.2.2.2.1
        exact ⟨hpi, by omega, by omega, by omega⟩
      obtain ⟨s', t, hx, ht, hf', hs'⟩ := backEdgeProg_refines h hf v u hvd hud hrv hru hfree
        (by omega) hvw huw (by simpa only [hrawV, optionWord] using hdvTag)
        (by simpa only [hrawU, optionWord] using hduTag) (by omega) (by omega) hparent
      refine ⟨s', 6 + (5 + t), Exec.ite_false eparent (Exec.ite_true edepth (by decide) hx),
        by omega, hf', ?_⟩
      simp only [visitedSearch, hdv, hdu, Option.getD_some, hlt]
      split
      · exact hs'
      · rename_i hnback
        exact False.elim (hnback ⟨hp, True.intro⟩)
    · have hltTag : ¬du + 1 < dv + 1 := by omega
      simp only [hltTag, decide_false, Bool.toNat_false] at edepth
      refine ⟨s, 12, Exec.ite_false eparent (Exec.ite_false edepth (Exec.skip s)), by omega, hf, ?_⟩
      simpa only [visitedSearch, hp, hdv, hdu, Option.getD_some, hlt, not_false_eq_true,
        and_false, ↓reduceIte] using h

end GraphMinor.Compute.PlanarityRam
