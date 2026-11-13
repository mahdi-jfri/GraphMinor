module

public import GraphMinor.Compute.PlanarityRamSolveTrim

/-!
# Pools of summaries

The solver keeps one summary for each finished vertex whose summary has not
yet been used, one current summary, and during an edge one child summary.
On the RAM these live in the same arenas, so the proof must know that they
use disjoint cells: a write to one summary must not change another.

`PoolAt s M K sl ptr bsOf nsOf` says that slot `v < K` holds the summary
`sl v` at record `ptr v` with blocks `bsOf v` and returns `nsOf v`, that
different slots own different blocks, returns and records, and that all of
them lie below the three bump allocators in registers 53 (returns), 54
(blocks) and 55 (records). The allocators never move back, so fresh cells
are never owned.

`PoolAt.update` is the one rule used for every step of the solver: some slots
`T` change, the cells written avoid the other slots, and the new contents of
the changed slots are built from their old cells and fresh cells.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The number of returns of an optional summary. -/
def nodeCnt : Option Summary → ℕ
  | none => 0
  | some S => nodeCount S

theorem weight_eq (o : Option Summary) : weight o = 120 * blockCount o + 10 * nodeCnt o := by
  cases o <;> rfl

theorem OptSummaryAt.nodes_length {s : State} {M p : ℕ} {o : Option Summary} {bs ns : List ℕ}
    (h : OptSummaryAt s M p o bs ns) : ns.length = nodeCnt o := by
  cases o with
  | none => obtain ⟨_, _, rfl⟩ := h; rfl
  | some S => exact SummaryAt.nodes_length h

theorem OptSummaryAt.frame {s s' : State} {M p : ℕ} {o : Option Summary} {bs ns : List ℕ}
    {W : ℕ → ℕ → Prop} (h : OptSummaryAt s M p o bs ns) (hF : Frame s s' W)
    (hp : p ≠ 0 → ¬ SummaryCell W p) (hb : ∀ q ∈ bs, ¬ BlockCell W q)
    (hn : ∀ q ∈ ns, ¬ NodeCell W q) : OptSummaryAt s' M p o bs ns := by
  cases o with
  | none => exact h
  | some S => exact SummaryAt.frame h hF (hp (Nat.ne_of_gt (SummaryAt.ptr_pos h).1)) hb hn

theorem OptSummaryAt.ptr_lt {s : State} {M p : ℕ} {o : Option Summary} {bs ns : List ℕ}
    (h : OptSummaryAt s M p o bs ns) : p < M + 1 := by
  cases o with
  | none => obtain ⟨rfl, _, _⟩ := h; omega
  | some S => exact (SummaryAt.ptr_pos h).2

/-- Summaries in slots `v < K` with disjoint cells below the allocators. -/
def PoolAt (s : State) (M K : ℕ) (sl : ℕ → Option Summary) (ptr : ℕ → ℕ)
    (bsOf nsOf : ℕ → List ℕ) : Prop :=
  (∀ v < K, OptSummaryAt s M (ptr v) (sl v) (bsOf v) (nsOf v)) ∧
  (∀ v < K, (∀ q ∈ nsOf v, q < s.regs 53) ∧ (∀ q ∈ bsOf v, q < s.regs 54) ∧
    ptr v < s.regs 55) ∧
  (∀ u < K, ∀ v < K, u ≠ v → (∀ q ∈ nsOf u, q ∉ nsOf v) ∧ (∀ q ∈ bsOf u, q ∉ bsOf v) ∧
    (ptr u ≠ 0 → ptr u ≠ ptr v))

/-- The update rule for pools. The slots `T` change, the frame avoids the
other slots, and the new cells of the slots `T` are old cells of slots `T`
or fresh cells. -/
theorem PoolAt.update {s s' : State} {M K : ℕ} {sl sl' : ℕ → Option Summary}
    {ptr ptr' : ℕ → ℕ} {bsOf nsOf bsOf' nsOf' : ℕ → List ℕ} {W : ℕ → ℕ → Prop} (T : ℕ → Prop)
    (hP : PoolAt s M K sl ptr bsOf nsOf) (hF : Frame s s' W)
    (h53 : s.regs 53 ≤ s'.regs 53) (h54 : s.regs 54 ≤ s'.regs 54)
    (h55 : s.regs 55 ≤ s'.regs 55)
    (hkeep : ∀ v < K, ¬ T v → sl' v = sl v ∧ ptr' v = ptr v ∧ bsOf' v = bsOf v ∧
      nsOf' v = nsOf v)
    (havoid : ∀ v < K, ¬ T v → (ptr v ≠ 0 → ¬ SummaryCell W (ptr v)) ∧
      (∀ q ∈ bsOf v, ¬ BlockCell W q) ∧ (∀ q ∈ nsOf v, ¬ NodeCell W q))
    (hnew : ∀ v < K, T v → OptSummaryAt s' M (ptr' v) (sl' v) (bsOf' v) (nsOf' v) ∧
      (∀ q ∈ nsOf' v, q < s'.regs 53) ∧ (∀ q ∈ bsOf' v, q < s'.regs 54) ∧ ptr' v < s'.regs 55)
    (hsrcN : ∀ v < K, T v → ∀ q ∈ nsOf' v, (∃ u < K, T u ∧ q ∈ nsOf u) ∨ s.regs 53 ≤ q)
    (hsrcB : ∀ v < K, T v → ∀ q ∈ bsOf' v, (∃ u < K, T u ∧ q ∈ bsOf u) ∨ s.regs 54 ≤ q)
    (hsrcP : ∀ v < K, T v → ptr' v ≠ 0 →
      (∃ u < K, T u ∧ ptr u ≠ 0 ∧ ptr' v = ptr u) ∨ s.regs 55 ≤ ptr' v)
    (hdisT : ∀ u < K, ∀ v < K, T u → T v → u ≠ v → (∀ q ∈ nsOf' u, q ∉ nsOf' v) ∧
      (∀ q ∈ bsOf' u, q ∉ bsOf' v) ∧ (ptr' u ≠ 0 → ptr' u ≠ ptr' v)) :
    PoolAt s' M K sl' ptr' bsOf' nsOf' := by
  obtain ⟨hrep, hbnd, hdis⟩ := hP
  -- A changed slot and a kept slot are disjoint.
  have hmix : ∀ u < K, ∀ v < K, T u → ¬ T v → (∀ q ∈ nsOf' u, q ∉ nsOf' v) ∧
      (∀ q ∈ bsOf' u, q ∉ bsOf' v) ∧ (ptr' u ≠ 0 → ptr' u ≠ ptr' v) ∧
      (ptr' v ≠ 0 → ptr' v ≠ ptr' u) := by
    intro u hu v hv hTu hTv
    obtain ⟨-, hpv, hbv, hnv⟩ := hkeep v hv hTv
    rw [hpv, hbv, hnv]
    refine ⟨fun q hq hq' => ?_, fun q hq hq' => ?_, fun hp he => ?_, fun hp he => ?_⟩
    · rcases hsrcN u hu hTu q hq with ⟨u', hu', hT', hq''⟩ | hq''
      · exact (hdis u' hu' v hv (fun e => hTv (e ▸ hT'))).1 q hq'' hq'
      · have := (hbnd v hv).1 q hq'; omega
    · rcases hsrcB u hu hTu q hq with ⟨u', hu', hT', hq''⟩ | hq''
      · exact (hdis u' hu' v hv (fun e => hTv (e ▸ hT'))).2.1 q hq'' hq'
      · have := (hbnd v hv).2.1 q hq'; omega
    · rcases hsrcP u hu hTu hp with ⟨u', hu', hT', hp', he'⟩ | hp'
      · exact (hdis u' hu' v hv (fun e => hTv (e ▸ hT'))).2.2 hp' (he' ▸ he)
      · have := (hbnd v hv).2.2; omega
    · by_cases hpu : ptr' u = 0
      · exact hp (he.trans hpu)
      rcases hsrcP u hu hTu hpu with ⟨u', hu', hT', hp', he'⟩ | hp'
      · exact (hdis v hv u' hu' (fun e => hTv (e ▸ hT'))).2.2 hp (he.trans he')
      · have := (hbnd v hv).2.2; omega
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun u hu v hv huv => ?_⟩
  · by_cases hT : T v
    · exact (hnew v hv hT).1
    · obtain ⟨hs, hp, hb, hn⟩ := hkeep v hv hT
      obtain ⟨hp', hb', hn'⟩ := havoid v hv hT
      rw [hs, hp, hb, hn]
      exact (hrep v hv).frame hF hp' hb' hn'
  · by_cases hT : T v
    · exact (hnew v hv hT).2
    · obtain ⟨-, hp, hb, hn⟩ := hkeep v hv hT
      rw [hp, hb, hn]
      obtain ⟨h1, h2, h3⟩ := hbnd v hv
      exact ⟨fun q hq => by have := h1 q hq; omega, fun q hq => by have := h2 q hq; omega,
        by omega⟩
  · by_cases hTu : T u
    · by_cases hTv : T v
      · exact hdisT u hu v hv hTu hTv huv
      · obtain ⟨h1, h2, h3, -⟩ := hmix u hu v hv hTu hTv
        exact ⟨h1, h2, h3⟩
    · by_cases hTv : T v
      · obtain ⟨h1, h2, -, h4⟩ := hmix v hv u hu hTv hTu
        exact ⟨fun q hq hq' => h1 q hq' hq, fun q hq hq' => h2 q hq' hq, h4⟩
      · obtain ⟨-, hpu, hbu, hnu⟩ := hkeep u hu hTu
        obtain ⟨-, hpv, hbv, hnv⟩ := hkeep v hv hTv
        rw [hpu, hbu, hnu, hpv, hbv, hnv]
        exact hdis u hu v hv huv

end GraphMinor.Compute.PlanarityRam
