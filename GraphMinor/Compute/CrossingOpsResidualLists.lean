module

public import GraphMinor.Compute.CrossingOpsResidual
public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Residual adjacency lists after a BFS pass

The residual lists remove the two possible orientations of each discovery-parent edge.
They represent graph difference and have no more entries than the original lists. The
parent-word test implements this filter in linear time.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Numerical endpoint test for an edge outside the discovery forest. -/
def withoutParentKeep {N : ℕ} (edges : List (Fin N × Fin N)) (x y : ℕ) : Bool :=
  if hx : x < N then if hy : y < N then
    decide ((⟨x, hx⟩, ⟨y, hy⟩) ∉ edges ∧ (⟨y, hy⟩, ⟨x, hx⟩) ∉ edges)
  else false else false

/-- The numerical adjacency list after removing a discovery forest. -/
def residualList {N : ℕ} (lists : Fin N → List ℕ) (edges : List (Fin N × Fin N))
    (x : ℕ) : List ℕ := (listOf lists x).filter (withoutParentKeep edges x)

/-- The residual numerical lists represent the difference graph. -/
theorem isAdjListFamily_residualList {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) (edges : List (Fin N × Fin N)) :
    IsAdjListFamily (G \ bfsDiscoveryForest edges) (fun u => residualList lists edges u.val) := by
  intro u
  simp only [residualList, listOf_fin]
  refine ⟨fun y hy => (h u).1 y (List.mem_of_mem_filter hy), (h u).2.1.filter _,
    (List.length_filter_le _ _).trans (h u).2.2.1, ?_⟩
  intro v
  simp only [List.mem_filter, withoutParentKeep, u.isLt, v.isLt, dite_true,
    decide_eq_true_eq, (h u).2.2.2 v, SimpleGraph.sdiff_adj, bfsDiscoveryForest,
    SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hg, huv, hvu⟩
    exact ⟨hg, fun hh => hh.2.elim huv hvu⟩
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun hh => hf ⟨hg.ne, Or.inl hh⟩, fun hh => hf ⟨hg.ne, Or.inr hh⟩⟩

/-- Filtering the packed lists cannot increase their total length. -/
theorem length_flatUpTo_residualList_le {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) (edges : List (Fin N × Fin N)) :
    (flatUpTo (residualList lists edges) N).length ≤ 2 * G.edgeSet.ncard := by
  rw [length_flatUpTo]
  calc
    (∑ x ∈ Finset.range N, (residualList lists edges x).length) ≤
        ∑ x ∈ Finset.range N, (listOf lists x).length :=
      Finset.sum_le_sum (fun _ _ => List.length_filter_le _ _)
    _ = 2 * G.edgeSet.ncard := by
      rw [← length_flatUpTo]
      exact length_flatUpTo_eq (fun u => by simpa [listOf_fin] using h u)

/-- Removing the forest edges from one list implements the residual numerical list. -/
theorem residualListProg_exec {w N : ℕ} (a_s a_e a_ent a_par buf R : ℕ)
    {s : State} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {edges : List (Fin N × Fin N)} {pre : List ℕ} {x st en k : ℕ}
    (hent : a_ent ≠ buf) (hparbuf : a_par ≠ buf)
    (hadj : IsAdjListFamily G lists) (hxN : x < N)
    (hl : IsListAt a_s a_e a_ent x st en (listOf lists x) s)
    (hp : IsBfsParentsAt a_par edges s) (hx : s.regs R = x)
    (hb : IsBuf buf (R + 4) pre k s) (hk : (residualList lists edges x).length ≤ k)
    (hN : N < 2 ^ w) (hen : en < 2 ^ w) (hw : 1 < 2 ^ w)
    (hcap : pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (filterListProg a_s a_e a_ent buf R
      (withoutParentTest a_par R (R + 3))) s s' t ∧
      t ≤ 9 + 30 * (listOf lists x).length ∧
      IsBuf buf (R + 4) (pre ++ residualList lists edges x)
        (k - (residualList lists edges x).length) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → s'.regs r = s.regs r) := by
  have hlt : ∀ y ∈ listOf lists x, y < N := by
    simpa only [listOf, dif_pos hxN] using (hadj ⟨x, hxN⟩).1
  obtain ⟨s', t, he, ht, hb', ha, hr⟩ := filterListProg_exec a_s a_e a_ent buf R
    (withoutParentTest a_par R (R + 3)) (withoutParentKeep edges x)
    hent hl hx hb hk (fun y hy => (hlt y hy).trans hN) (hxN.trans hN) hen hw hcap
    (fun z y hy ha hx' hy' => by
      have hyN := hlt y hy
      have hh := eval_withoutParentTest (hp.of_arrs_eq (ha a_par hparbuf))
        ⟨x, hxN⟩ ⟨y, hyN⟩ hx' hy' hN hw
      simpa only [withoutParentKeep, hxN, hyN, dite_true, decide_eq_true_eq] using hh)
  exact ⟨s', t, he, by simpa only [withoutParentTest, Expr.cost, Nat.mul_comm] using ht,
    hb', ha, hr⟩

end GraphMinor.Compute.Crossing
