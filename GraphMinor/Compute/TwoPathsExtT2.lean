module

public import GraphMinor.Compute.TwoPathsCompChain

/-!
# Undoing the collapse edges on vertex lists

The last part of the extraction undoes the collapse edges (the collapse stage of the completion),
the last one first, with no search (`undoT2Edge` and `undoT2Chain`,
`GraphMinor/HP25/Sec5UndoT2.lean`, after Claim 5.5 of Humeau and Pous, page 19). A program sees a
crossing only as the two vertex lists of its paths, and a collapse step only as its record `y, z, N`
(`aT2Rec`). This file states what `undoT2Edge` does in those terms, so that a program can follow it.

* `bypassList`: the vertex list of `p.bypass`, computed from the vertex list of `p`
  (`support_bypass`).
* `undoT2Lists y z N Q R`: if `N` is not empty and `y z` is an edge of the list `Q`, then `Q`
  becomes `bypassList (rule2PocketChain y z N Q)`; otherwise the same test and change are made on
  `R`; otherwise nothing changes.
* `undoT2Edge_lists`: for a valid crossing, `undoT2Edge` returns a crossing with the same ends
  whose two vertex lists are `undoT2Lists` of the old ones. The reason is that the walk transfer
  to the graph `G₀` before the step fails exactly when the walk uses `y z` and `y z` is not an edge
  of `G₀`. The second condition holds exactly when `N` is not empty, since the path `P₀` of the
  step is induced.
* `undoT2Chain_lists`: the same for a whole `T2Chain`, with `undoT2All`, which applies
  `undoT2Lists` to the steps of the chain, last step first.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {V : Type*} [DecidableEq V]

/-- The vertex list of the bypass of a walk with vertex list `l` (`support_bypass`). -/
def bypassList : List V → List V
  | [] => []
  | u :: rest =>
    if u ∈ bypassList rest then (bypassList rest).drop ((bypassList rest).idxOf u)
    else u :: bypassList rest

/-- Are `y` and `z` next to each other in the list `l`? (`listHasEdge_iff`) -/
def listHasEdge (y z : V) (l : List V) : Bool :=
  (l.zip l.tail).any fun p => (p.1 = y ∧ p.2 = z) ∨ (p.1 = z ∧ p.2 = y)

/-- The test of a collapse step `y, z, N` on the vertex list `l` of a path of a crossing: the window
is not empty and `y z` is an edge of `l`. -/
def t2Uses (y z : V) (N l : List V) : Bool := !N.isEmpty && listHasEdge y z l

/-- Undo one collapse step `y, z, N` on the vertex lists `Q`, `R` of a crossing. -/
def undoT2Lists (y z : V) (N Q R : List V) : List V × List V :=
  if t2Uses y z N Q then (bypassList (rule2PocketChain y z N Q), R)
  else if t2Uses y z N R then (Q, bypassList (rule2PocketChain y z N R))
  else (Q, R)

/-- Undo the collapse steps `steps`, in the order of the list, on the vertex lists of a crossing.
The extraction gives the steps last added first. -/
def undoT2All : List (V × V × List V) → List V × List V → List V × List V
  | [], qr => qr
  | (y, z, N) :: rest, qr => undoT2All rest (undoT2Lists y z N qr.1 qr.2)

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {V : Type*} [DecidableEq V]

public section

/-- The bypass of a walk has the vertex list `bypassList` of the walk's vertex list. -/
theorem support_bypass {G : SimpleGraph V} : ∀ {u v : V} (p : G.Walk u v),
    p.bypass.support = bypassList p.support
  | _, _, .nil => rfl
  | u, _, .cons h p => by
    have ih := support_bypass p
    simp only [Walk.bypass, Walk.support_cons, bypassList]
    rw [← ih]
    split_ifs with hu
    · rw [Walk.dropUntil_eq_drop, Walk.support_copy, Walk.drop_support_eq_support_drop_min]
      have h1 := List.idxOf_lt_length_iff.mpr (ih ▸ hu)
      have h2 := p.bypass.length_support
      rw [ih] at h2
      rw [ih, Nat.min_eq_left (by omega)]
    · rfl

theorem listHasEdge_iff (y z : V) (l : List V) : listHasEdge y z l = true ↔ IsListEdge l y z := by
  unfold listHasEdge IsListEdge
  simp only [List.any_eq_true, decide_eq_true_eq]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  rw [eq_comm, Sym2.eq_iff]
  tauto

theorem t2Uses_iff (y z : V) (N l : List V) : t2Uses y z N l = true ↔ N ≠ [] ∧ IsListEdge l y z := by
  simp [t2Uses, listHasEdge_iff]

omit [DecidableEq V] in
/-- `y z` is an edge of a walk exactly when it is an edge of its vertex list. -/
theorem mem_edges_iff_isListEdge {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (y z : V) :
    s(y, z) ∈ p.edges ↔ IsListEdge p.support y z := by
  rw [Walk.edges_eq_zipWith_support, ← List.map_uncurry_zip_eq_zipWith, List.mem_map]
  constructor
  · rintro ⟨q, hq, he⟩
    exact ⟨q, hq, he.symm⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨q, hq, he.symm⟩

variable {C A B : List V} {a b : V} {k : ℕ}

/-- The edge `y z` of a collapse step is an edge of the graph before the step exactly when its
window `N` is empty: an edge between two vertices of the induced path `P₀` is an edge of the
path. -/
theorem t2Step_adj_iff (step : T2Step V C A B a b k) : step.G₀.Adj step.y step.z ↔ step.N = [] := by
  have hnd : step.P₀.support.Nodup := step.hP₀.1.support_nodup
  have hch := step.P₀.isChain_adj_support
  rw [step.hsupp] at hnd hch
  constructor
  · intro h
    have hle := step.hind step.y (by rw [step.hsupp]; simp) step.z (by rw [step.hsupp]; simp) h
    rw [step.hsupp] at hle
    have hi := hle.idxOf hnd
    have hy : (step.L₁ ++ step.y :: step.N ++ step.z :: step.L₂).idxOf step.y = step.L₁.length := by
      have := hnd.idxOf_getElem step.L₁.length (by simp)
      simpa using this
    have hz : (step.L₁ ++ step.y :: step.N ++ step.z :: step.L₂).idxOf step.z =
        step.L₁.length + 1 + step.N.length := by
      have := hnd.idxOf_getElem (step.L₁.length + 1 + step.N.length) (by simp; omega)
      rw [← this]
      congr 1
      rw [List.getElem_append_right (by simp; omega)]
      have h0 : step.L₁.length + 1 + step.N.length - (step.L₁ ++ step.y :: step.N).length = 0 := by
        simp; omega
      simp only [h0, List.getElem_cons_zero]
    rw [hy, hz] at hi
    exact List.eq_nil_of_length_eq_zero (by omega)
  · intro h
    rw [h] at hch
    have : [step.y, step.z].IsChain step.G₀.Adj :=
      hch.infix ⟨step.L₁, step.L₂, by simp⟩
    simpa using this

omit [DecidableEq V] in
/-- The transfer of a walk of `G₀ + yz` to `G₀` fails only if the walk uses `y z`, and it fails
when the walk uses `y z` and `y z` is not an edge of `G₀`. -/
theorem transferWalkOption_eq_none_iff {G₀ : SimpleGraph V} [DecidableRel G₀.Adj] {y z : V}
    (hyz : ¬ G₀.Adj y z) : ∀ {u v : V} (p : (G₀ ⊔ edge y z).Walk u v),
    transferWalkOption (G := G₀) p = none ↔ s(y, z) ∈ p.edges
  | _, _, .nil => by simp [transferWalkOption]
  | _, _, .cons (u := x) (v := x') h p => by
    have ih := transferWalkOption_eq_none_iff hyz p
    simp only [transferWalkOption, Walk.edges_cons, List.mem_cons]
    by_cases hG : G₀.Adj x x'
    · simp only [hG, ↓reduceDIte]
      have hne : s(y, z) ≠ s(x, x') := by
        intro he
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hyz hG
        · exact hyz hG.symm
      rcases ho : transferWalkOption (G := G₀) p with _ | q
      · simp only [ho, true_iff] at ih
        simp only [true_iff]
        exact Or.inr ih
      · simp only [ho, reduceCtorEq, false_iff] at ih ⊢
        tauto
    · simp only [hG, ↓reduceDIte, true_iff]
      left
      rcases h with h | h
      · exact absurd h hG
      · simp only [edge_adj] at h
        rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap

/-- The test of `undoT2Lists` on the vertex list of a walk of the graph after a collapse step:
it holds exactly when the transfer of the walk to the graph before the step fails. -/
theorem t2Step_transfer_none_iff (step : T2Step V C A B a b k) [DecidableRel step.G₀.Adj]
    {u v : V} (p : step.G₁.Walk u v) :
    transferWalkOption (G := step.G₀) p = none ↔ step.N ≠ [] ∧ IsListEdge p.support step.y step.z := by
  by_cases hN : step.N = []
  · simp only [hN, ne_eq, not_true_eq_false, false_and, iff_false]
    intro h
    have hadj : step.G₀.Adj step.y step.z := (t2Step_adj_iff step).mpr hN
    have hle : step.G₁ ≤ step.G₀ := by
      intro x x' hx
      rcases hx with hx | hx
      · exact hx
      · simp only [edge_adj] at hx
        rcases hx.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact hadj.symm
    have key : ∀ {u v : V} (p : step.G₁.Walk u v), transferWalkOption (G := step.G₀) p ≠ none := by
      intro u v p
      induction p with
      | nil => simp [transferWalkOption]
      | cons h p ih =>
        simp only [transferWalkOption, hle h, ↓reduceDIte]
        rcases ho : transferWalkOption (G := step.G₀) p with _ | q
        · exact absurd ho ih
        · simp
    exact key p h
  · have hyz : ¬ step.G₀.Adj step.y step.z := fun h => hN ((t2Step_adj_iff step).mp h)
    rw [show transferWalkOption (G := step.G₀) p = none ↔ s(step.y, step.z) ∈ p.edges from
      transferWalkOption_eq_none_iff hyz p, mem_edges_iff_isListEdge]
    simp [hN]

/-- `walkOfChainTo` gives a walk with vertex list `c :: X.tail`. -/
theorem walkOfChainTo_support {G : SimpleGraph V} [DecidableRel G.Adj] {c d : V} {X : List V}
    {p : G.Walk c d} (h : walkOfChainTo G c d X = some p) : p.support = c :: X.tail := by
  have aux : ∀ {x : V} {rest : List V} {v : V} {q : G.Walk x v},
      walkOfChainAux G x rest = some ⟨v, q⟩ → q.support = x :: rest := by
    intro x rest
    induction rest generalizing x with
    | nil =>
      intro v q h
      simp only [walkOfChainAux, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases eq_of_heq h
      rfl
    | cons y rest ih =>
      intro v q h
      simp only [walkOfChainAux] at h
      split_ifs at h with hxy
      rcases ho : walkOfChainAux G y rest with _ | ⟨v', q'⟩ <;> rw [ho] at h
      · simp at h
      · simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        cases eq_of_heq h
        simp [ih ho]
  unfold walkOfChainTo at h
  rcases ho : walkOfChainAux G c X.tail with _ | ⟨v, q⟩ <;> rw [ho] at h
  · simp at h
  · simp only at h
    split_ifs at h with hv
    subst hv
    cases h
    exact aux ho

/-- **`undoT2Edge` on vertex lists.** For a valid crossing of `C` after a collapse step,
`undoT2Edge` returns a valid crossing with the same ends whose vertex lists are those that
`undoT2Lists` computes from the old ones. -/
theorem undoT2Edge_lists (step : T2Step V C A B a b k) [DecidableRel step.G₀.Adj]
    {cr : CrossingWalks step.G₁ C} (hcr : cr.Valid) :
    ∃ cr₀, undoT2Edge step cr = some cr₀ ∧ cr₀.Valid ∧ cr₀.u₁ = cr.u₁ ∧ cr₀.v₁ = cr.v₁ ∧
      cr₀.u₂ = cr.u₂ ∧ cr₀.v₂ = cr.v₂ ∧
      (cr₀.Q.support, cr₀.R.support) =
        undoT2Lists step.y step.z step.N cr.Q.support cr.R.support := by
  obtain ⟨cr₀, h₀, hv₀⟩ := undoT2Edge_spec step hcr
  refine ⟨cr₀, h₀, hv₀, ?_⟩
  have hQ := t2Step_transfer_none_iff step cr.Q
  have hR := t2Step_transfer_none_iff step cr.R
  unfold undoT2Edge at h₀
  unfold undoT2Lists
  rcases hQo : transferWalkOption (G := step.G₀) cr.Q with _ | Q₀ <;>
    rcases hRo : transferWalkOption (G := step.G₀) cr.R with _ | R₀ <;>
    rw [hQo, hRo] at h₀ <;> simp only at h₀
  · simp at h₀
  · have hQt : step.N ≠ [] ∧ IsListEdge cr.Q.support step.y step.z := hQ.mp hQo
    rw [show t2Uses step.y step.z step.N cr.Q.support = true from (t2Uses_iff _ _ _ _).mpr hQt]
    simp only [↓reduceIte]
    rcases hw : walkOfChainTo step.G₀ cr.u₁ cr.v₁
      (rule2PocketChain step.y step.z step.N cr.Q.support) with _ | p <;> rw [hw] at h₀
    · simp at h₀
    · simp only [Option.some.injEq] at h₀
      subst h₀
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      have hQe : s(step.y, step.z) ∈ cr.Q.edges := (mem_edges_iff_isListEdge _ _ _).mpr hQt.2
      obtain ⟨-, hh, -⟩ := rule2PocketChain_spec step.hP₀ step.hsupp cr.Q hcr.2.1 hQe
      have hps := walkOfChainTo_support hw
      have hX : cr.u₁ :: (rule2PocketChain step.y step.z step.N cr.Q.support).tail =
          rule2PocketChain step.y step.z step.N cr.Q.support := by
        exact List.cons_head?_tail hh
      simp only [support_bypass, hps, hX, transferWalkOption_support hRo]
  · have hQt : ¬ (step.N ≠ [] ∧ IsListEdge cr.Q.support step.y step.z) := fun h => by
      rw [hQ.mpr h] at hQo; simp at hQo
    have hRt : step.N ≠ [] ∧ IsListEdge cr.R.support step.y step.z := hR.mp hRo
    rw [show t2Uses step.y step.z step.N cr.Q.support = false from
      Bool.eq_false_iff.mpr fun h => hQt ((t2Uses_iff _ _ _ _).mp h),
      show t2Uses step.y step.z step.N cr.R.support = true from (t2Uses_iff _ _ _ _).mpr hRt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hw : walkOfChainTo step.G₀ cr.u₂ cr.v₂
      (rule2PocketChain step.y step.z step.N cr.R.support) with _ | p <;> rw [hw] at h₀
    · simp at h₀
    · simp only [Option.some.injEq] at h₀
      subst h₀
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      have hRe : s(step.y, step.z) ∈ cr.R.edges := (mem_edges_iff_isListEdge _ _ _).mpr hRt.2
      obtain ⟨-, hh, -⟩ := rule2PocketChain_spec step.hP₀ step.hsupp cr.R hcr.2.2.1 hRe
      have hps := walkOfChainTo_support hw
      have hX : cr.u₂ :: (rule2PocketChain step.y step.z step.N cr.R.support).tail =
          rule2PocketChain step.y step.z step.N cr.R.support := by
        exact List.cons_head?_tail hh
      simp only [support_bypass, hps, hX, transferWalkOption_support hQo]
  · simp only [Option.some.injEq] at h₀
    subst h₀
    have hQt : ¬ (step.N ≠ [] ∧ IsListEdge cr.Q.support step.y step.z) := fun h => by
      rw [hQ.mpr h] at hQo; simp at hQo
    have hRt : ¬ (step.N ≠ [] ∧ IsListEdge cr.R.support step.y step.z) := fun h => by
      rw [hR.mpr h] at hRo; simp at hRo
    rw [show t2Uses step.y step.z step.N cr.Q.support = false from
      Bool.eq_false_iff.mpr fun h => hQt ((t2Uses_iff _ _ _ _).mp h),
      show t2Uses step.y step.z step.N cr.R.support = false from
      Bool.eq_false_iff.mpr fun h => hRt ((t2Uses_iff _ _ _ _).mp h)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    rw [transferWalkOption_support hQo, transferWalkOption_support hRo]

/-- **`undoT2Chain` on vertex lists.** For a valid crossing of `C` in the graph at the end of a
`T2Chain`, `undoT2Chain` returns a valid crossing of `C` in the graph at its start, with the same
ends, whose vertex lists are those that `undoT2All` computes from the old ones. -/
theorem undoT2Chain_lists {G H : SimpleGraph V} (chain : T2Chain V C A B a b k G H)
    {cr : CrossingWalks H C} (hcr : cr.Valid) :
    ∃ crG, undoT2Chain chain cr = some crG ∧ crG.Valid ∧ crG.u₁ = cr.u₁ ∧ crG.v₁ = cr.v₁ ∧
      crG.u₂ = cr.u₂ ∧ crG.v₂ = cr.v₂ ∧
      (crG.Q.support, crG.R.support) =
        undoT2All (t2Steps chain).reverse (cr.Q.support, cr.R.support) := by
  induction chain with
  | nil => exact ⟨cr, rfl, hcr, rfl, rfl, rfl, rfl, rfl⟩
  | snoc step dec chain ih =>
    let _ := dec
    obtain ⟨cr₀, h₀, hv₀, e1, e2, e3, e4, hl₀⟩ := undoT2Edge_lists step hcr
    obtain ⟨crG, hG, hvG, f1, f2, f3, f4, hlG⟩ := ih hv₀
    refine ⟨crG, by simp only [undoT2Chain, h₀, hG], hvG, f1.trans e1, f2.trans e2, f3.trans e3,
      f4.trans e4, ?_⟩
    rw [hlG, t2Steps, List.reverse_append, List.reverse_singleton, List.singleton_append,
      undoT2All, ← hl₀]

end

end GraphMinor.Compute.TwoPaths
