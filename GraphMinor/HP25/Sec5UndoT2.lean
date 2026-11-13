module

public import GraphMinor.HP25.Sec5Search
public import GraphMinor.HP25.Sec5Tight
import GraphMinor.HP25.Sec5UndoExhaust

/-!
# Undoing a collapsed edge with no search

The collapse stage of the completion (`Sec5Collapse.lean`) adds an edge `y z` across a window
`N` of an induced `C`-path `P` whose vertices are on no side. Claim 5.5 of Humeau and Pous
(page 19) says that the edge is safe. Its proof is a rerouting: in a crossing of `C` in `G + yz`,
the path through `yz` is rerouted along `y N z`, and the other path misses `N`, because
"$\{y_j,y_r\}$ separates them from $C$" (`not_mem_window_of_tPath`).

This file turns that proof into a function with no search and no fallback. `T2Step` holds the data
and the hypotheses of `claim_5_5_of`. `undoT2Edge` takes a crossing of `C` in `G + yz` and returns a
crossing of `C` in `G`: it keeps both paths when neither uses `yz`, and otherwise replaces `yz` by
`y N z` in the path that uses it. `undoT2Edge_spec` proves that it returns `some` valid crossing
for every valid crossing, with no other hypothesis.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*}

/-- **Data of one collapse step.** The edge `y z` is added across the window `N` of an
induced `C`-path `P₀` of `G₀`, under the hypotheses of Claim 5.5 (`claim_5_5_of`): the window
condition and no vertex of `N` on a side. -/
structure T2Step (V : Type*) (C A B : List V) (a b : V) (k : ℕ) where
  /-- Graph before adding the edge `y z`. -/
  G₀ : SimpleGraph V
  /-- First endpoint of the added edge. -/
  y : V
  /-- Second endpoint of the added edge. -/
  z : V
  /-- Prefix of `P₀` before `y`. -/
  L₁ : List V
  /-- Window of `P₀` strictly between `y` and `z`. -/
  N : List V
  /-- Suffix of `P₀` after `z`. -/
  L₂ : List V
  /-- The `C`-path before adding `y z`. -/
  P₀ : G₀.Walk a b
  /-- `C` rotated by `k` is `a :: A ++ b :: B`. -/
  hrot : C.rotate k = a :: A ++ b :: B
  /-- `P₀` is a `C`-path of `G₀`. -/
  hP₀ : IsTPath G₀ C P₀
  /-- Support decomposition `P₀.support = L₁ ++ y :: N ++ z :: L₂`. -/
  hsupp : P₀.support = L₁ ++ y :: N ++ z :: L₂
  /-- `P₀` is induced in `G₀`. -/
  hind : ∀ u ∈ P₀.support, ∀ v ∈ P₀.support, G₀.Adj u v → IsListEdge P₀.support u v
  /-- The window condition. -/
  hwc : WindowClosed G₀ C A B P₀ y z N
  /-- No vertex of `N` is on a side. -/
  hno : ∀ v ∈ N, ¬ IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ A} v ∧
    ¬ IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} v

variable {C A B : List V} {a b : V} {k : ℕ}

/-- The graph after adding `edge step.y step.z`. -/
@[expose] def T2Step.G₁ (step : T2Step V C A B a b k) : SimpleGraph V :=
  step.G₀ ⊔ edge step.y step.z

/-- The walk from `c` to `d` along a vertex list, when the list is a chain from `c` to `d`. -/
@[expose] def walkOfChainTo (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] (c d : V)
    (X : List V) : Option (G.Walk c d) :=
  match walkOfChainAux G c X.tail with
  | some ⟨v, p⟩ => if h : v = d then some (h ▸ p) else none
  | none => none

theorem walkOfChainTo_eq_some {G : SimpleGraph V} [DecidableRel G.Adj] [DecidableEq V]
    {X : List V} {c d : V} (hch : X.IsChain G.Adj) (hh : X.head? = some c)
    (hl : X.getLast? = some d) :
    ∃ p : G.Walk c d, walkOfChainTo G c d X = some p ∧ p.support = X := by
  cases X with
  | nil => simp at hh
  | cons x rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    obtain ⟨p, hp, hsupp⟩ := walkOfChainAux_eq_some_of_isChain hch hl
    exact ⟨p, by simp [walkOfChainTo, hp], hsupp⟩

/-- **Undo a collapse edge (no search).** Keep both paths when neither uses `y z`; otherwise replace
`y z` by `y N z` in the path that uses it, and shorten that walk to a path. -/
@[expose] def undoT2Edge [DecidableEq V] (step : T2Step V C A B a b k)
    [DecidableRel step.G₀.Adj] (cr : CrossingWalks step.G₁ C) : Option (CrossingWalks step.G₀ C) :=
  match transferWalkOption (G := step.G₀) cr.Q, transferWalkOption (G := step.G₀) cr.R with
  | some Q₀, some R₀ => some ⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, Q₀, R₀⟩
  | none, some R₀ =>
    match walkOfChainTo step.G₀ cr.u₁ cr.v₁ (rule2PocketChain step.y step.z step.N cr.Q.support) with
    | some p => some ⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, p.bypass, R₀⟩
    | none => none
  | some Q₀, none =>
    match walkOfChainTo step.G₀ cr.u₂ cr.v₂ (rule2PocketChain step.y step.z step.N cr.R.support) with
    | some p => some ⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, Q₀, p.bypass⟩
    | none => none
  | none, none => none

/-- The rerouted path: if `Q` uses `y z` and `R₀` is a `C`-path of `G₀` disjoint from `Q`, the
walk along `rule2PocketChain` exists, is a `C`-path of `G₀`, and misses `R₀`. -/
private theorem reroute_spec [DecidableEq V] (step : T2Step V C A B a b k)
    [DecidableRel step.G₀.Adj] {u₁ v₁ u₂ v₂ : V} (Q : step.G₁.Walk u₁ v₁)
    (hQ : IsTPath step.G₁ C Q) (hQe : s(step.y, step.z) ∈ Q.edges)
    (R₀ : step.G₀.Walk u₂ v₂) (hR₀ : IsTPath step.G₀ C R₀)
    (hdisj : Q.support.Disjoint R₀.support) :
    ∃ p : step.G₀.Walk u₁ v₁,
      walkOfChainTo step.G₀ u₁ v₁ (rule2PocketChain step.y step.z step.N Q.support) = some p ∧
      IsTPath step.G₀ C p.bypass ∧ p.bypass.support.Disjoint R₀.support := by
  obtain ⟨hch, hh, hl, hsub, hC⟩ :=
    rule2PocketChain_spec (G₀ := step.G₀) step.hP₀ step.hsupp Q hQ hQe
  obtain ⟨p, hp, hps⟩ := walkOfChainTo_eq_some hch hh hl
  refine ⟨p, hp, ⟨p.bypass_isPath, hQ.2.1, hQ.2.2.1, fun x hx hxu hxv => ?_⟩, ?_⟩
  · have hxX : x ∈ rule2PocketChain step.y step.z step.N Q.support := by
      have h := p.support_bypass_subset_support hx
      rwa [hps] at h
    by_cases hxC : x ∈ C
    · rcases hC x hxX hxC with rfl | rfl
      · exact absurd rfl hxu
      · exact absurd rfl hxv
    · exact ⟨hxC, hxC⟩
  · have hyR : step.y ∉ R₀.support := fun h => hdisj (Q.fst_mem_support_of_mem_edges hQe) h
    have hzR : step.z ∉ R₀.support := fun h => hdisj (Q.snd_mem_support_of_mem_edges hQe) h
    have hNR := not_mem_window_of_tPath step.hrot step.hP₀ step.hsupp step.hind step.hwc step.hno
      R₀ hR₀ hyR hzR
    intro x hx hxR
    have hxX : x ∈ rule2PocketChain step.y step.z step.N Q.support := by
      have h := p.support_bypass_subset_support hx
      rwa [hps] at h
    rcases hsub x hxX with hxQ | hxN
    · exact hdisj hxQ hxR
    · exact hNR x hxN hxR

/-- **`undoT2Edge` is complete and sound** (Claim 5.5, Humeau and Pous, page 19, as a function):
for every valid crossing of `C` in `G₀ + yz` it returns `some` valid crossing of `C` in `G₀`. -/
theorem undoT2Edge_spec [DecidableEq V] (step : T2Step V C A B a b k)
    [DecidableRel step.G₀.Adj] {cr : CrossingWalks step.G₁ C} (hcr : cr.Valid) :
    ∃ cr₀, undoT2Edge step cr = some cr₀ ∧ cr₀.Valid := by
  obtain ⟨hidx, hQ, hR, hdisj⟩ := hcr
  unfold undoT2Edge
  rcases hQo : transferWalkOption (G := step.G₀) cr.Q with _ | Q₀ <;>
    rcases hRo : transferWalkOption (G := step.G₀) cr.R with _ | R₀
  · exact absurd (hdisj (cr.Q.fst_mem_support_of_mem_edges (mem_edges_of_transferWalkOption_none hQo))
      (cr.R.fst_mem_support_of_mem_edges (mem_edges_of_transferWalkOption_none hRo))) id
  · have hR₀ := transferWalkOption_isTPath hRo hR
    have hRs := transferWalkOption_support hRo
    obtain ⟨p, hp, hpT, hpd⟩ := reroute_spec step cr.Q hQ (mem_edges_of_transferWalkOption_none hQo)
      R₀ hR₀ (by rw [hRs]; exact hdisj)
    exact ⟨⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, p.bypass, R₀⟩, by simp [hp], hidx, hpT, hR₀, hpd⟩
  · have hQ₀ := transferWalkOption_isTPath hQo hQ
    have hQs := transferWalkOption_support hQo
    obtain ⟨p, hp, hpT, hpd⟩ := reroute_spec step cr.R hR (mem_edges_of_transferWalkOption_none hRo)
      Q₀ hQ₀ (by rw [hQs]; exact hdisj.symm)
    exact ⟨⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, Q₀, p.bypass⟩, by simp [hp], hidx, hQ₀, hpT, hpd.symm⟩
  · exact ⟨_, rfl, hidx, transferWalkOption_isTPath hQo hQ, transferWalkOption_isTPath hRo hR,
      by rw [transferWalkOption_support hQo, transferWalkOption_support hRo]; exact hdisj⟩

/-- A run of collapse steps from `G` to `H`, first step first. -/
inductive T2Chain (V : Type*) (C A B : List V) (a b : V) (k : ℕ) (G : SimpleGraph V) :
    SimpleGraph V → Type _
  | nil : T2Chain V C A B a b k G G
  | snoc (step : T2Step V C A B a b k) (dec : DecidableRel step.G₀.Adj)
      (chain : T2Chain V C A B a b k G step.G₀) :
      T2Chain V C A B a b k G step.G₁

/-- Undo the collapse edges of a `T2Chain` in reverse order (no search). -/
@[expose] def undoT2Chain [DecidableEq V] {G H : SimpleGraph V} :
    T2Chain V C A B a b k G H → CrossingWalks H C → Option (CrossingWalks G C)
  | .nil, cr => some cr
  | .snoc step dec chain, cr =>
    let _ := dec
    match undoT2Edge step cr with
    | some cr₀ => undoT2Chain chain cr₀
    | none => none

/-- **`undoT2Chain` is complete and sound:** for every valid crossing of `C` in `H` it returns
`some` valid crossing of `C` in `G`. -/
theorem undoT2Chain_spec [DecidableEq V] {G H : SimpleGraph V}
    (chain : T2Chain V C A B a b k G H) {cr : CrossingWalks H C} (hcr : cr.Valid) :
    ∃ crG, undoT2Chain chain cr = some crG ∧ crG.Valid := by
  induction chain with
  | nil => exact ⟨cr, rfl, hcr⟩
  | snoc step dec chain ih =>
    obtain ⟨cr₀, h₀, hv₀⟩ := undoT2Edge_spec step hcr
    obtain ⟨crG, hG, hvG⟩ := ih hv₀
    exact ⟨crG, by simp only [undoT2Chain, h₀, hG], hvG⟩

end GraphMinor.HP25
