module

public import GraphMinor.Crossing.Statements
import GraphMinor.Crossing.CutSec2Flow
public import GraphMinor.Compute.SpecsCrossing
public import GraphMinor.Compute.MengerAugment
public import GraphMinor.Compute.Restrict

/-!
# Combinatorial Bridge for the Bounded-Flow Program (Sections 2.1 and 2.2)

This file connects the path-system and residual-search invariants of `PathSystem.lean` and
`MengerAugment.lean` on the active subgraph `activeGraph G S z ow` to the split network
`splitCap (apex G D) (flowVerts S ow) (some z) none k` of Sections 2.1 and 2.2 of
`docs/crossing/crossing_extractor.tex`:

- `pathSystemFlow`: turns a valid `A`-`B` path system `(used, pred, succ)` on
  `activeGraph G S z ow` into a `0`/`1`-valued flow in the split network of `apex G D` on
  `flowVerts S ow` from `(some z, true)` to `(none, false)` of value `(pathStarts used pred).card`.
- `isUnseparable_of_disjointPathFamily` and `isUnseparable_of_pathSystem_card_eq`: when
  `(pathStarts used pred).card = k` (`1 ≤ k`), `Sec21PathsStatement` yields `k` internally disjoint
  paths and hence `IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1)`.
- `not_resReach_of_resPopClosed`: when the forward residual BFS stops with
  `IsResPopClosed` and reaches no `outNode b` (`b ∈ B`), `(some z, true)` cannot reach
  `(none, false)` in `ResAdj (splitCap ...) (pathSystemFlow ...)`.
- `IsRevResClosed` and `mem_extractCut_iff_of_revClosed`: characterizes the extracted minimum
  separator `extractCut (apex G D) (flowVerts S ow) (some z) none k f` via reverse residual
  reachability from `{outNode b | b ∈ B}`.
- `mem_sourceSide_iff_not_reachable`: characterizes `sourceSide (apex G D) (flowVerts S ow) none X`
  via reachability from `D \ X` in `restrictGraph G V_rem`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute

/-! ### Section 1: Active Vertices, Active Graph, and Terminal Sets -/

/-- The active `Fin N` vertices of a bounded-flow query: vertices of `S` excluding `ow` and `z`. -/
def activeVerts {N : ℕ} (S : Finset (Fin N)) (z : Fin N) (ow : ℕ) : Finset (Fin N) :=
  S.filter (fun v => v.val ≠ ow ∧ v ≠ z)

/-- The subgraph of `G` induced on `activeVerts S z ow`. -/
def activeGraph {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) (z : Fin N) (ow : ℕ) :
    SimpleGraph (Fin N) :=
  restrictGraph G (activeVerts S z ow)

open Classical in
/-- Active neighbors of the source `z` in `G`. -/
noncomputable def sourceNeighbors {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (z : Fin N) (ow : ℕ) : Finset (Fin N) :=
  (activeVerts S z ow).filter (fun u => G.Adj z u)

/-- Active vertices lying on the cycle `D` (neighbors of the apex sink `none` in `apex G D`). -/
def sinkNeighbors {N : ℕ} (S : Finset (Fin N)) (D : List (Fin N)) (z : Fin N) (ow : ℕ) :
    Finset (Fin N) :=
  (activeVerts S z ow).filter (fun u => u ∈ D)

theorem some_mem_flowVerts_iff {N : ℕ} {S : Finset (Fin N)} {ow : ℕ} (v : Fin N) :
    some v ∈ flowVerts S ow ↔ v ∈ S ∧ v.val ≠ ow := by
  unfold flowVerts apexVerts
  by_cases how : ow < N
  · simp [how]
    simp [Fin.ext_iff]
  · have hne : v.val ≠ ow := by have := v.2; omega
    simp [how, hne]

theorem none_mem_flowVerts {N : ℕ} (S : Finset (Fin N)) (ow : ℕ) :
    (none : Option (Fin N)) ∈ flowVerts S ow := by
  unfold flowVerts apexVerts
  split_ifs <;> simp

theorem some_z_mem_flowVerts {N : ℕ} {S : Finset (Fin N)} {z : Fin N} {ow : ℕ}
    (hz : z ∈ S) (how : ow ≠ z.val) :
    some z ∈ flowVerts S ow := by
  rw [some_mem_flowVerts_iff]
  exact ⟨hz, how.symm⟩

theorem not_apex_adj_some_z_none {N : ℕ} (G : SimpleGraph (Fin N)) {D : List (Fin N)} {z : Fin N}
    (hzD : z ∉ D) :
    ¬ (apex G D).Adj (some z) none :=
  hzD

theorem mem_activeVerts_iff {N : ℕ} {S : Finset (Fin N)} {z : Fin N} {ow : ℕ} (v : Fin N) :
    v ∈ activeVerts S z ow ↔ some v ∈ flowVerts S ow ∧ v ≠ z := by
  simp only [activeVerts, Finset.mem_filter, some_mem_flowVerts_iff, and_assoc]

theorem mem_sourceNeighbors_iff {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {z : Fin N} {ow : ℕ} (u : Fin N) :
    u ∈ sourceNeighbors G S z ow ↔ u ∈ activeVerts S z ow ∧ G.Adj z u := by
  simp [sourceNeighbors]

theorem mem_sinkNeighbors_iff {N : ℕ} {S : Finset (Fin N)} {D : List (Fin N)}
    {z : Fin N} {ow : ℕ} (u : Fin N) :
    u ∈ sinkNeighbors S D z ow ↔ u ∈ activeVerts S z ow ∧ u ∈ D := by
  simp [sinkNeighbors]

theorem used_mem_activeVerts {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {ow : ℕ} {used pred succ : Fin N → ℕ}
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    {u : Fin N} (hu : used u ≠ 0) :
    u ∈ activeVerts S z ow := by
  have hp_le := hsys.pred_le u
  rcases eq_or_lt_of_le hp_le with hp_eq | hp_lt
  · have huA := hsys.start_mem_A u hu hp_eq
    exact (mem_sourceNeighbors_iff u).mp huA |>.1
  · let w : Fin N := ⟨pred u, hp_lt⟩
    have hsucc : succ w = u.val := (hsys.succ_iff_pred w u).mpr rfl
    have hadj := (hsys.adj_of_succ w u hsucc).2.2
    exact hadj.2.1

theorem used_z_eq_zero {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {ow : ℕ} {used pred succ : Fin N → ℕ}
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ) :
    used z = 0 := by
  by_contra hne
  have hz_act := used_mem_activeVerts hsys hne
  rw [mem_activeVerts_iff] at hz_act
  exact hz_act.2 rfl

/-! ### Section 2: Split-Network Flow Associated to a Path System -/

/-- The `0`/`1` flow in the split network of `apex G D` induced by a path system
`(used, pred, succ)` on `activeGraph G S z ow`. -/
def pathSystemFlow {N : ℕ} (z : Fin N) (used pred succ : Fin N → ℕ) :
    Option (Fin N) × Bool → Option (Fin N) × Bool → ℕ
  | (some u, false), (some v, true) => if u = v then used u else 0
  | (some u, true), (some v, false) =>
      if u = z then (if used v ≠ 0 ∧ pred v = N then 1 else 0)
      else (if used u ≠ 0 ∧ succ u = v.val then 1 else 0)
  | (some u, true), (none, false) =>
      if u = z then 0 else (if used u ≠ 0 ∧ succ u = N then 1 else 0)
  | _, _ => 0

private theorem sum_option_bool_nat {N : ℕ} (g : Option (Fin N) × Bool → ℕ) :
    (∑ b : Option (Fin N) × Bool, g b) =
      g (none, false) + g (none, true) +
        ∑ u : Fin N, (g (some u, false) + g (some u, true)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  simp only [Fintype.sum_bool, add_comm (g (none, true)) (g (none, false)),
    add_comm (g (some _, true)) (g (some _, false))]

private theorem sum_option_bool_int {N : ℕ} (g : Option (Fin N) × Bool → ℤ) :
    (∑ b : Option (Fin N) × Bool, g b) =
      g (none, false) + g (none, true) +
        ∑ u : Fin N, (g (some u, false) + g (some u, true)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  simp only [Fintype.sum_bool, add_comm (g (none, true)) (g (none, false)),
    add_comm (g (some _, true)) (g (some _, false))]

theorem pathSystemFlow_le_one {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {ow : ℕ} {used pred succ : Fin N → ℕ}
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    (a b : Option (Fin N) × Bool) :
    pathSystemFlow z used pred succ a b ≤ 1 := by
  have hle := hsys.used_le
  rcases a with ⟨_|u, _|_|_⟩ <;> rcases b with ⟨_|v, _|_|_⟩ <;>
    simp only [pathSystemFlow] <;> (try split_ifs) <;> first | exact hle _ | omega

theorem pathSystemFlow_le_splitCap {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    (hz : z ∈ S) (how : ow ≠ z.val)
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    (a b : Option (Fin N) × Bool) :
    pathSystemFlow z used pred succ a b ≤
      splitCap (apex G D) (flowVerts S ow) (some z) none k a b := by
  rcases a with ⟨_|u, _|_|_⟩ <;> rcases b with ⟨_|v, _|_|_⟩
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · simp [pathSystemFlow]
  · -- (some u, false) -> (some v, true)
    simp only [pathSystemFlow, splitCap]
    by_cases huv : u = v
    · subst huv
      by_cases hu : used u = 0
      · simp [hu]
      · have hu_act := used_mem_activeVerts hsys hu
        have hu_flow : some u ∈ flowVerts S ow := (mem_activeVerts_iff u).mp hu_act |>.1
        have hu_le := hsys.used_le u
        simp only [↓reduceIte, true_and, hu_flow]
        split_ifs <;> omega
    · simp [huv]
  · -- (some u, true) -> (none, false)
    simp only [pathSystemFlow, splitCap]
    by_cases huz : u = z
    · simp [huz]
    · simp only [huz, ↓reduceIte]
      by_cases hcond : used u ≠ 0 ∧ succ u = N
      · have huB := hsys.end_mem_B u hcond.1 hcond.2
        rcases (mem_sinkNeighbors_iff u).mp huB with ⟨hu_act, huD⟩
        have hu_flow : some u ∈ flowVerts S ow := (mem_activeVerts_iff u).mp hu_act |>.1
        have hnone_flow : (none : Option (Fin N)) ∈ flowVerts S ow := none_mem_flowVerts S ow
        have hadj : (apex G D).Adj (some u) none := huD
        simp [hcond, hu_flow, hnone_flow, hadj]
      · simp [hcond]
  · simp [pathSystemFlow]
  · -- (some u, true) -> (some v, false)
    simp only [pathSystemFlow, splitCap]
    by_cases huz : u = z
    · rw [huz]
      simp only [↓reduceIte]
      by_cases hcond : used v ≠ 0 ∧ pred v = N
      · have hvA := hsys.start_mem_A v hcond.1 hcond.2
        rcases (mem_sourceNeighbors_iff v).mp hvA with ⟨hv_act, hadjG⟩
        have hz_flow : some z ∈ flowVerts S ow := some_z_mem_flowVerts hz how
        have hv_flow : some v ∈ flowVerts S ow := (mem_activeVerts_iff v).mp hv_act |>.1
        have hadj : (apex G D).Adj (some z) (some v) := hadjG
        simp [hcond, hz_flow, hv_flow, hadj]
      · simp [hcond]
    · simp only [huz, ↓reduceIte]
      by_cases hcond : used u ≠ 0 ∧ succ u = v.val
      · have hadj_act := (hsys.adj_of_succ u v hcond.2).2.2
        have hu_flow : some u ∈ flowVerts S ow := (mem_activeVerts_iff u).mp hadj_act.1 |>.1
        have hv_flow : some v ∈ flowVerts S ow := (mem_activeVerts_iff v).mp hadj_act.2.1 |>.1
        have hadj : (apex G D).Adj (some u) (some v) := hadj_act.2.2
        simp [hcond, hu_flow, hv_flow, hadj]
      · simp [hcond]
  · simp [pathSystemFlow]

theorem isFlow_pathSystemFlow {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    (hz : z ∈ S) (how : ow ≠ z.val)
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ) :
    IsFlow (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (some z, true) (none, false) (pathSystemFlow z used pred succ) := by
  refine ⟨pathSystemFlow_le_splitCap hz how hsys, ?_⟩
  intro a ha_src ha_snk
  rcases a with ⟨_|u, _|_|_⟩
  · exact absurd rfl ha_snk
  · -- a = (none, true)
    rw [sum_option_bool_nat, sum_option_bool_nat]
    simp [pathSystemFlow]
  · -- a = (some u, false)
    rw [sum_option_bool_nat, sum_option_bool_nat]
    have hout : (∑ v : Fin N, if u = v then used u else 0) = used u := by
      simp
    simp only [pathSystemFlow, zero_add, add_zero, hout]
    by_cases hu0 : used u = 0
    · rw [hu0]
      apply Finset.sum_eq_zero
      intro w _
      split_ifs with hwz h1 h2
      · exact absurd rfl h1.1
      · rfl
      · exfalso
        exact (hsys.adj_of_succ w u h2.2).2.1 hu0
      · rfl
    · have hu1 : used u = 1 := by have := hsys.used_le u; omega
      have hp_le := hsys.pred_le u
      rcases eq_or_lt_of_le hp_le with hp_eq | hp_lt
      · -- pred u = N: inflow comes only from w = z
        have hsum : (∑ w : Fin N,
            if w = z then (if used u ≠ 0 ∧ pred u = N then 1 else 0)
            else (if used w ≠ 0 ∧ succ w = u.val then 1 else 0)) =
            ∑ w : Fin N, if w = z then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          by_cases hwz : w = z
          · subst hwz
            simp [hu0, hp_eq.symm]
          · simp only [hwz, ↓reduceIte]
            by_cases hcond : used w ≠ 0 ∧ succ w = u.val
            · exfalso
              have hpred : pred u = w.val := (hsys.succ_iff_pred w u).mp hcond.2
              have := w.2
              omega
            · simp [hcond]
        rw [hsum, hu1]
        simp
      · -- pred u < N: inflow comes only from w = ⟨pred u, hp_lt⟩
        let w₀ : Fin N := ⟨pred u, hp_lt⟩
        have hsucc₀ : succ w₀ = u.val := (hsys.succ_iff_pred w₀ u).mpr rfl
        have hw₀_used : used w₀ ≠ 0 := (hsys.adj_of_succ w₀ u hsucc₀).1
        have hw₀_ne_z : w₀ ≠ z := by
          intro h
          rw [h] at hw₀_used
          exact hw₀_used (used_z_eq_zero hsys)
        have hp_ne_N : pred u ≠ N := by omega
        have hsum : (∑ w : Fin N,
            if w = z then (if used u ≠ 0 ∧ pred u = N then 1 else 0)
            else (if used w ≠ 0 ∧ succ w = u.val then 1 else 0)) =
            ∑ w : Fin N, if w = w₀ then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          by_cases hww₀ : w = w₀
          · subst hww₀
            simp [hw₀_ne_z, hw₀_used, hsucc₀]
          · by_cases hwz : w = z
            · subst hwz
              simp [hp_ne_N, hww₀]
            · simp only [hwz, hww₀, ↓reduceIte]
              have hnot : ¬ (used w ≠ 0 ∧ succ w = u.val) := by
                rintro ⟨_, hsw⟩
                have hpw : pred u = w.val := (hsys.succ_iff_pred w u).mp hsw
                apply hww₀
                ext
                exact hpw.symm
              simp [hnot]
        rw [hsum, hu1]
        simp
  · -- a = (some u, true) with u ≠ z
    have huz : u ≠ z := fun h => ha_src (by simp [h])
    rw [sum_option_bool_nat, sum_option_bool_nat]
    have hin : (∑ w : Fin N, if w = u then used w else 0) = used u := by
      simp
    simp only [pathSystemFlow, huz, ↓reduceIte, zero_add, add_zero, hin]
    by_cases hu0 : used u = 0
    · simp [hu0]
    · have hu1 : used u = 1 := by have := hsys.used_le u; omega
      have hs_le := hsys.succ_le u
      rcases eq_or_lt_of_le hs_le with hs_eq | hs_lt
      · -- succ u = N
        have hsum : (∑ v : Fin N, if used u ≠ 0 ∧ succ u = v.val then 1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v _
          have hne : succ u ≠ v.val := by have := v.2; omega
          simp [hne]
        rw [hsum, hu1]
        simp [hs_eq.symm]
      · -- succ u < N
        let v₀ : Fin N := ⟨succ u, hs_lt⟩
        have hs_ne_N : succ u ≠ N := by omega
        have hsum : (∑ v : Fin N, if used u ≠ 0 ∧ succ u = v.val then 1 else 0) =
            ∑ v : Fin N, if v = v₀ then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          by_cases hvv₀ : v = v₀
          · subst hvv₀
            simp [hu0, v₀]
          · have hne : succ u ≠ v.val := fun h => hvv₀ (Fin.ext h.symm)
            simp [hvv₀, hne]
        rw [hsum, hu1]
        simp [hs_ne_N]

theorem flowValue_pathSystemFlow {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {ow : ℕ} {used pred succ : Fin N → ℕ}
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ) :
    flowValue (some z, true) (pathSystemFlow z used pred succ) =
      ((pathStarts used pred).card : ℤ) := by
  unfold flowValue
  rw [sum_option_bool_int, sum_option_bool_int]
  have hz0 : used z = 0 := used_z_eq_zero hsys
  simp only [pathSystemFlow, ↓reduceIte, Nat.cast_zero, add_zero, zero_add]
  have hin : (∑ u : Fin N, ((if u = z then used u else 0 : ℕ) : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    split_ifs with huz
    · subst huz; simp [hz0]
    · rfl
  rw [hin, sub_zero, pathStarts, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> rfl

/-! ### Section 3: Disjoint Path Family Implies Unseparability -/

theorem isUnseparable_of_disjointPathFamily {W : Type*} [DecidableEq W]
    (J : SimpleGraph W) (T : Set W) (z x : W) {k : ℕ} (hk : 1 ≤ k)
    (P : Fin k → J.Walk z x) (hP : IsDisjointPathFamily J T z x P) :
    IsUnseparable J T z x (k - 1) := by
  intro X hX hcard
  by_contra hnot_reach
  have hex : ∀ i : Fin k, ∃ y ∈ X, y ∈ (P i).support := by
    intro i
    by_contra! hall
    apply hnot_reach
    refine ⟨P i, fun y hy => ⟨hP.2.1 i y hy, ?_⟩⟩
    intro hyX
    exact hall y hyX hy
  choose g hgX hgsup using hex
  have hmaps : Set.MapsTo g (↑(Finset.univ : Finset (Fin k))) (↑X) := by
    intro i _
    exact Finset.mem_coe.mpr (hgX i)
  have hinj : Set.InjOn g (↑(Finset.univ : Finset (Fin k))) := by
    intro i _ j _ hij_eq
    by_contra hij_ne
    have hzx := hP.2.2 i j hij_ne (g i) (hgsup i) (by rw [hij_eq]; exact hgsup j)
    have hmem : (g i : W) ∈ T \ {z, x} := hX (Finset.mem_coe.mpr (hgX i))
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact hmem.2 hzx
  have hle := Finset.card_le_card_of_injOn g hmaps hinj
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

theorem isUnseparable_of_pathSystem_card_eq
    {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    (hz : z ∈ S) (hzD : z ∉ D) (hk : 1 ≤ k) (how : ow ≠ z.val)
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    (hcard : (pathStarts used pred).card = k) :
    IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1) := by
  have hflow := isFlow_pathSystemFlow (k := k) hz how hsys
  have hval : flowValue (some z, true) (pathSystemFlow z used pred succ) = (k : ℤ) := by
    rw [flowValue_pathSystemFlow hsys, hcard]
  rcases sec21Paths_proved.{0} (apex G D) (flowVerts S ow) (some z) none k k (pathSystemFlow z used pred succ)
      (some_z_mem_flowVerts hz how) (none_mem_flowVerts S ow) (Option.some_ne_none z)
      (not_apex_adj_some_z_none G hzD) hflow hval with ⟨P, hP⟩
  exact isUnseparable_of_disjointPathFamily (apex G D) (flowVerts S ow) (some z) none hk P hP

/-! ### Section 4: Forward Residual Closure and Non-Reachability -/

theorem inNode_mem_activeVerts_of_resParentInv {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {z : Fin N} {ow : ℕ}
    {used pred succ : Fin N → ℕ} {a_parent : ℕ} {items : List ℕ} {s : State}
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    (hpar_inv : ResParentInv (activeGraph G S z ow) (sourceNeighbors G S z ow)
      used pred succ a_parent items s)
    {v : Fin N} (hv : v.val ∈ items) :
    v ∈ activeVerts S z ow := by
  rcases hpar_inv.2.2.1 v hv with ⟨_, hvA⟩ | ⟨w, _, _, _, hw_cases⟩
  · exact (mem_sourceNeighbors_iff v).mp hvA |>.1
  · rcases hw_cases with ⟨rfl, hw_ne⟩ | ⟨_, hadj⟩
    · exact used_mem_activeVerts hsys hw_ne
    · exact hadj.2.1

theorem outNode_mem_activeVerts_of_resParentInv {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {z : Fin N} {ow : ℕ}
    {used pred succ : Fin N → ℕ} {a_parent : ℕ} {items : List ℕ} {s : State}
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    (hpar_inv : ResParentInv (activeGraph G S z ow) (sourceNeighbors G S z ow)
      used pred succ a_parent items s)
    {w : Fin N} (hw : w.val + N ∈ items) :
    w ∈ activeVerts S z ow := by
  rcases hpar_inv.2.2.2 w hw with ⟨u, _, hu_it, _, hres⟩
  rw [residualAdj_inNode_outNode_iff] at hres
  rcases hres with ⟨_, rfl⟩ | ⟨_, hpu⟩
  · exact inNode_mem_activeVerts_of_resParentInv hsys hpar_inv hu_it
  · have hsucc : succ w = u.val := (hsys.succ_iff_pred w u).mpr hpu
    exact (hsys.adj_of_succ w u hsucc).2.2.1

private theorem splitCap_out_in_pos {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {u v : Fin N} {m : ℕ}
    (h : m < splitCap (apex G D) (flowVerts S ow) (some z) none k (some u, true) (some v, false)) :
    some u ∈ flowVerts S ow ∧ some v ∈ flowVerts S ow ∧ G.Adj u v := by
  simp only [splitCap] at h
  split_ifs at h with hcond
  · exact ⟨hcond.1, hcond.2.1, hcond.2.2⟩
  · omega

private theorem splitCap_out_none_pos {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {u : Fin N} {m : ℕ}
    (h : m < splitCap (apex G D) (flowVerts S ow) (some z) none k (some u, true) (none, false)) :
    some u ∈ flowVerts S ow ∧ u ∈ D := by
  simp only [splitCap] at h
  split_ifs at h with hcond
  · exact ⟨hcond.1, hcond.2.2⟩
  · omega

/-- The subset of split-network nodes reached by the forward residual BFS `items`. -/
def fwdReachedSet {N : ℕ} (z : Fin N) (items : List ℕ) : Set (Option (Fin N) × Bool)
  | (some u, false) => u = z ∨ u.val ∈ items
  | (some u, true) => u = z ∨ u.val + N ∈ items
  | (none, _) => False

theorem not_resReach_of_resPopClosed {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {a_parent : ℕ} {items : List ℕ} {s : State}
    (hzD : z ∉ D)
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    (hpar_inv : ResParentInv (activeGraph G S z ow) (sourceNeighbors G S z ow)
      used pred succ a_parent items s)
    (hclosed : IsResPopClosed (activeGraph G S z ow) used pred succ items items.length)
    (hA_items : ∀ a ∈ sourceNeighbors G S z ow, a.val ∈ items)
    (hB_not_items : ∀ b ∈ sinkNeighbors S D z ow, b.val + N ∉ items) :
    ¬ ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some z, true) (none, false) := by
  have hstep_closed : ∀ a b : Option (Fin N) × Bool,
      a ∈ fwdReachedSet z items →
      ResAdj (splitCap (apex G D) (flowVerts S ow) (some z) none k)
        (pathSystemFlow z used pred succ) a b →
      b ∈ fwdReachedSet z items := by
    intro a b ha hadj
    rcases a with ⟨_|u, _|_|_⟩
    · exact False.elim ha
    · exact False.elim ha
    · -- a = (some u, false), so u = z ∨ u.val ∈ items
      rcases b with ⟨_|v, _|_|_⟩
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
      · -- b = (some v, true)
        change v = z ∨ v.val + N ∈ items
        by_cases hvz : v = z
        · exact Or.inl hvz
        · right
          rcases (ha : u = z ∨ u.val ∈ items) with huz | hu_it
          · -- u = z, v ≠ z
            subst huz
            exfalso
            rcases hadj with hcap | hpos
            · simp [splitCap, pathSystemFlow, Ne.symm hvz] at hcap
            · simp only [pathSystemFlow, hvz, ↓reduceIte] at hpos
              split_ifs at hpos with hcond
              · have hz_ne := (hsys.adj_of_succ v u hcond.2).2.1
                exact hz_ne (used_z_eq_zero hsys)
              · omega
          · -- u.val ∈ items, v ≠ z
            rcases hadj with hcap | hpos
            · simp only [splitCap, pathSystemFlow] at hcap
              by_cases huv : u = v
              · subst huv
                have hu_le := hsys.used_le u
                have hu0 : used u = 0 := by
                  by_contra hne
                  have hu1 : used u = 1 := by omega
                  by_cases hcond : some u ∈ flowVerts S ow <;>
                    simp [hu1, hvz, hcond] at hcap
                have hres : ResidualAdj (activeGraph G S z ow) used pred succ
                    (inNode u) (outNode u) := by
                  rw [residualAdj_inNode_outNode_iff]
                  exact Or.inl ⟨hu0, rfl⟩
                exact hclosed.to_closed (inNode u) (outNode u) hu_it hres
              · simp [huv] at hcap
            · simp only [pathSystemFlow, hvz, ↓reduceIte] at hpos
              split_ifs at hpos with hcond
              · have hp : pred u = v.val := (hsys.succ_iff_pred v u).mp hcond.2
                have hu_ne : used u ≠ 0 := (hsys.adj_of_succ v u hcond.2).2.1
                have hres : ResidualAdj (activeGraph G S z ow) used pred succ
                    (inNode u) (outNode v) := by
                  rw [residualAdj_inNode_outNode_iff]
                  exact Or.inr ⟨hu_ne, hp⟩
                exact hclosed.to_closed (inNode u) (outNode v) hu_it hres
              · omega
    · -- a = (some u, true), so u = z ∨ u.val + N ∈ items
      rcases b with ⟨_|v, _|_|_⟩
      · -- b = (none, false)
        exfalso
        rcases hadj with hcap | hpos
        · rcases splitCap_out_none_pos hcap with ⟨hu_flow, huD⟩
          have huz : u ≠ z := fun h => hzD (h ▸ huD)
          have hu_act : u ∈ activeVerts S z ow := (mem_activeVerts_iff u).mpr ⟨hu_flow, huz⟩
          have huB : u ∈ sinkNeighbors S D z ow := (mem_sinkNeighbors_iff u).mpr ⟨hu_act, huD⟩
          rcases (ha : u = z ∨ u.val + N ∈ items) with huz' | hu_it
          · exact huz huz'
          · exact hB_not_items u huB hu_it
        · simp [pathSystemFlow] at hpos
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
      · -- b = (some v, false)
        change v = z ∨ v.val ∈ items
        by_cases hvz : v = z
        · exact Or.inl hvz
        · right
          rcases (ha : u = z ∨ u.val + N ∈ items) with huz | hu_it
          · -- u = z
            subst huz
            rcases hadj with hcap | hpos
            · rcases splitCap_out_in_pos hcap with ⟨_, hv_flow, hadjG⟩
              have hv_act : v ∈ activeVerts S u ow := (mem_activeVerts_iff v).mpr ⟨hv_flow, hvz⟩
              have hvA : v ∈ sourceNeighbors G S u ow :=
                (mem_sourceNeighbors_iff v).mpr ⟨hv_act, hadjG⟩
              exact hA_items v hvA
            · simp [pathSystemFlow, hvz] at hpos
          · -- u.val + N ∈ items, v ≠ z
            have hu_act : u ∈ activeVerts S z ow :=
              outNode_mem_activeVerts_of_resParentInv hsys hpar_inv hu_it
            rcases hadj with hcap | hpos
            · rcases splitCap_out_in_pos hcap with ⟨_, hv_flow, hadjG⟩
              have hv_act : v ∈ activeVerts S z ow := (mem_activeVerts_iff v).mpr ⟨hv_flow, hvz⟩
              have hadj_act : (activeGraph G S z ow).Adj u v := ⟨hu_act, hv_act, hadjG⟩
              by_cases hsucc : v.val = succ u
              · rcases hpar_inv.2.2.2 u hu_it with ⟨w_p, _, hwp_it, _, hres_wp⟩
                rw [residualAdj_inNode_outNode_iff] at hres_wp
                have hu_ne : used u ≠ 0 := (hsys.adj_of_succ u v hsucc.symm).1
                rcases hres_wp with ⟨hw0, rfl⟩ | ⟨_, hpw⟩
                · exact absurd hw0 hu_ne
                · have hsucc_wp : succ u = w_p.val := (hsys.succ_iff_pred u w_p).mpr hpw
                  have hvw : v = w_p := Fin.ext (by omega)
                  rw [hvw]
                  exact hwp_it
              · have hres : ResidualAdj (activeGraph G S z ow) used pred succ
                    (outNode u) (inNode v) := by
                  rw [residualAdj_outNode_inNode_iff]
                  exact Or.inr ⟨hsucc, hadj_act⟩
                exact hclosed.to_closed (outNode u) (inNode v) hu_it hres
            · simp only [pathSystemFlow] at hpos
              split_ifs at hpos with hvu
              · subst hvu
                have hres : ResidualAdj (activeGraph G S z ow) used pred succ
                    (outNode v) (inNode v) := by
                  rw [residualAdj_outNode_inNode_iff]
                  exact Or.inl ⟨by omega, rfl⟩
                exact hclosed.to_closed (outNode v) (inNode v) hu_it hres
              · omega
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
  have hreach_sub : ∀ a b : Option (Fin N) × Bool,
      ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
        (pathSystemFlow z used pred succ) a b →
      a ∈ fwdReachedSet z items → b ∈ fwdReachedSet z items := by
    intro a b hr ha
    induction hr with
    | refl => exact ha
    | tail _ hstep ih => exact hstep_closed _ _ ih hstep
  intro hreach
  exact hreach_sub (some z, true) (none, false) hreach (Or.inl rfl)

/-! ### Section 5: Reverse Residual Search and Separator Extraction -/

/-- Soundness and closure invariant for the reverse residual BFS visited list `rev_items`
starting from `{outNode b | b ∈ sinkNeighbors S D z ow}`. -/
structure IsRevResClosed {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ)
    (rev_items : List ℕ) : Prop where
  in_active : ∀ v : Fin N, v.val ∈ rev_items → v ∈ activeVerts S z ow
  out_active : ∀ w : Fin N, w.val + N ∈ rev_items → w ∈ activeVerts S z ow
  in_sound : ∀ v : Fin N, v.val ∈ rev_items →
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some v, false) (none, false)
  out_sound : ∀ w : Fin N, w.val + N ∈ rev_items →
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some w, true) (none, false)
  sink_seeded : ∀ b ∈ sinkNeighbors S D z ow, b.val + N ∈ rev_items
  in_closed_used : ∀ v : Fin N, v.val ∈ rev_items → used v ≠ 0 → v.val + N ∈ rev_items
  in_closed_adj : ∀ v u : Fin N, v.val ∈ rev_items →
    (activeGraph G S z ow).Adj v u → u.val + N ∈ rev_items
  out_closed_unused : ∀ w : Fin N, w.val + N ∈ rev_items → used w = 0 → w.val ∈ rev_items
  out_closed_succ : ∀ w u : Fin N, w.val + N ∈ rev_items →
    used w ≠ 0 → succ w = u.val → u.val ∈ rev_items

theorem resReach_out_of_mem_sinkNeighbors {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    (hk : 1 ≤ k)
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    {b : Fin N} (hb : b ∈ sinkNeighbors S D z ow) :
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some b, true) (none, false) := by
  refine Relation.ReflTransGen.single (Or.inl ?_)
  rcases (mem_sinkNeighbors_iff b).mp hb with ⟨hb_act, hbD⟩
  have hb_flow : some b ∈ flowVerts S ow := (mem_activeVerts_iff b).mp hb_act |>.1
  have hnone_flow : (none : Option (Fin N)) ∈ flowVerts S ow := none_mem_flowVerts S ow
  have hadj : (apex G D).Adj (some b) none := hbD
  have hcap : splitCap (apex G D) (flowVerts S ow) (some z) none k (some b, true) (none, false) =
      k + 1 := by
    simp [splitCap, hb_flow, hnone_flow, hadj]
  have hfl := pathSystemFlow_le_one hsys (some b, true) (none, false)
  omega

theorem resReach_out_of_in_used {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {v : Fin N} (hused : used v ≠ 0)
    (hreach : ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some v, false) (none, false)) :
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some v, true) (none, false) := by
  refine .head (Or.inr ?_) hreach
  simp only [pathSystemFlow, ↓reduceIte]
  omega

theorem resReach_out_of_in_adj {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    (hk : 1 ≤ k)
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    {v u : Fin N} (hadj : (activeGraph G S z ow).Adj v u)
    (hreach : ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some v, false) (none, false)) :
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some u, true) (none, false) := by
  refine .head (Or.inl ?_) hreach
  have hv_flow : some v ∈ flowVerts S ow := (mem_activeVerts_iff v).mp hadj.1 |>.1
  have hu_flow : some u ∈ flowVerts S ow := (mem_activeVerts_iff u).mp hadj.2.1 |>.1
  have hadj_apex : (apex G D).Adj (some u) (some v) := hadj.2.2.symm
  have hcap : splitCap (apex G D) (flowVerts S ow) (some z) none k (some u, true) (some v, false) =
      k + 1 := by
    simp [splitCap, hu_flow, hv_flow, hadj_apex]
  have hfl := pathSystemFlow_le_one hsys (some u, true) (some v, false)
  omega

theorem resReach_in_of_out_unused {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {w : Fin N} (hw_act : w ∈ activeVerts S z ow) (hunused : used w = 0)
    (hreach : ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some w, true) (none, false)) :
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some w, false) (none, false) := by
  refine .head (Or.inl ?_) hreach
  have hw_flow : some w ∈ flowVerts S ow := (mem_activeVerts_iff w).mp hw_act |>.1
  simp only [splitCap, pathSystemFlow, ↓reduceIte, true_and, hw_flow, hunused]
  split_ifs <;> omega

theorem resReach_in_of_out_succ {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {w u : Fin N} (hw_act : w ∈ activeVerts S z ow) (hused : used w ≠ 0) (hsucc : succ w = u.val)
    (hreach : ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some w, true) (none, false)) :
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some u, false) (none, false) := by
  refine .head (Or.inr ?_) hreach
  have hwz : w ≠ z := (mem_activeVerts_iff w).mp hw_act |>.2
  simp [pathSystemFlow, hwz, hused, hsucc]

/-- Set of split-network nodes represented by `rev_items` together with `(none, _)`. -/
def revReachedSet {N : ℕ} (rev_items : List ℕ) : Set (Option (Fin N) × Bool)
  | (none, _) => True
  | (some v, false) => v.val ∈ rev_items
  | (some w, true) => w.val + N ∈ rev_items

theorem resReach_some_iff_mem_revReachedSet {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {rev_items : List ℕ}
    (hzD : z ∉ D) (hk : (pathStarts used pred).card ≤ k)
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    (hnot_reach : ¬ ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some z, true) (none, false))
    (hrev : IsRevResClosed G S D z k ow used pred succ rev_items)
    (v : Fin N) (b_dir : Bool) :
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some v, b_dir) (none, false) ↔
      (some v, b_dir) ∈ revReachedSet rev_items := by
  let _ := hk
  have hstep_rev : ∀ x b : Option (Fin N) × Bool,
      ResAdj (splitCap (apex G D) (flowVerts S ow) (some z) none k)
        (pathSystemFlow z used pred succ) x b →
      b ∈ revReachedSet rev_items →
      x ∈ revReachedSet rev_items := by
    intro x b hadj hb
    rcases b with ⟨_|v, _|_|_⟩
    · -- b = (none, false)
      rcases x with ⟨_|u, _|_|_⟩
      · exact trivial
      · exact trivial
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
      · -- x = (some u, true) -> (none, false)
        change u.val + N ∈ rev_items
        rcases hadj with hcap | hpos
        · rcases splitCap_out_none_pos hcap with ⟨hu_flow, huD⟩
          have huz : u ≠ z := fun h => hzD (h ▸ huD)
          have hu_act : u ∈ activeVerts S z ow := (mem_activeVerts_iff u).mpr ⟨hu_flow, huz⟩
          have huB : u ∈ sinkNeighbors S D z ow := (mem_sinkNeighbors_iff u).mpr ⟨hu_act, huD⟩
          exact hrev.sink_seeded u huB
        · simp [pathSystemFlow] at hpos
    · -- b = (none, true)
      rcases x with ⟨_|u, _|_|_⟩
      · exact trivial
      · exact trivial
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
    · -- b = (some v, false), so v.val ∈ rev_items
      have hv_it : v.val ∈ rev_items := hb
      have hv_act : v ∈ activeVerts S z ow := hrev.in_active v hv_it
      have hb_reach := hrev.in_sound v hv_it
      rcases x with ⟨_|u, _|_|_⟩
      · exact trivial
      · exact trivial
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
      · -- x = (some u, true) -> (some v, false)
        change u.val + N ∈ rev_items
        have huz : u ≠ z := by
          intro h
          subst h
          exact hnot_reach (.head hadj hb_reach)
        rcases hadj with hcap | hpos
        · rcases splitCap_out_in_pos hcap with ⟨hu_flow, _, hadjG⟩
          have hu_act : u ∈ activeVerts S z ow := (mem_activeVerts_iff u).mpr ⟨hu_flow, huz⟩
          have hadj_act : (activeGraph G S z ow).Adj v u := ⟨hv_act, hu_act, hadjG.symm⟩
          exact hrev.in_closed_adj v u hv_it hadj_act
        · simp only [pathSystemFlow] at hpos
          split_ifs at hpos with hvu
          · subst hvu
            exact hrev.in_closed_used v hv_it (by omega)
          · omega
    · -- b = (some v, true), so v.val + N ∈ rev_items
      have hv_it : v.val + N ∈ rev_items := hb
      have hv_act : v ∈ activeVerts S z ow := hrev.out_active v hv_it
      have hvz : v ≠ z := (mem_activeVerts_iff v).mp hv_act |>.2
      rcases x with ⟨_|u, _|_|_⟩
      · exact trivial
      · exact trivial
      · -- x = (some u, false) -> (some v, true)
        change u.val ∈ rev_items
        rcases hadj with hcap | hpos
        · simp only [splitCap, pathSystemFlow] at hcap
          by_cases huv : u = v
          · subst huv
            have hu_le := hsys.used_le u
            have hu0 : used u = 0 := by
              by_contra hne
              have hu1 : used u = 1 := by omega
              by_cases hcond : some u ∈ flowVerts S ow <;>
                simp [hu1, hvz, hcond] at hcap
            exact hrev.out_closed_unused u hv_it hu0
          · simp [huv] at hcap
        · simp only [pathSystemFlow, hvz, ↓reduceIte] at hpos
          split_ifs at hpos with hcond
          · exact hrev.out_closed_succ v u hv_it hcond.1 hcond.2
          · omega
      · rcases hadj with h | h <;> simp [splitCap, pathSystemFlow] at h
  have hreach_rev : ∀ x y : Option (Fin N) × Bool,
      ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
        (pathSystemFlow z used pred succ) x y →
      y ∈ revReachedSet rev_items → x ∈ revReachedSet rev_items := by
    intro x y hr hy
    induction hr with
    | refl => exact hy
    | tail _ hstep ih => exact ih (hstep_rev _ _ hstep hy)
  constructor
  · intro hreach
    exact hreach_rev (some v, b_dir) (none, false) hreach trivial
  · intro hmem
    rcases b_dir with _ | _
    · exact hrev.in_sound v hmem
    · exact hrev.out_sound v hmem

open Classical in
theorem mem_extractCut_iff_of_revClosed {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {rev_items : List ℕ}
    (hzD : z ∉ D) (hk : (pathStarts used pred).card ≤ k)
    (hsys : IsValidPathSystem (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) used pred succ)
    (hnot_reach : ¬ ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some z, true) (none, false))
    (hrev : IsRevResClosed G S D z k ow used pred succ rev_items)
    (v : Fin N) :
    some v ∈ extractCut (apex G D) (flowVerts S ow) (some z) none k
        (pathSystemFlow z used pred succ) ↔
      v.val ∉ rev_items ∧ v.val + N ∈ rev_items := by
  unfold extractCut
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold sinkCut
  simp only [Set.mem_ofPred_eq, not_not]
  rw [resReach_some_iff_mem_revReachedSet hzD hk hsys hnot_reach hrev v false,
    resReach_some_iff_mem_revReachedSet hzD hk hsys hnot_reach hrev v true]
  rfl

/-! ### Section 6: Source Side Characterization via Graph Reachability -/

/-- Remaining `Fin N` vertices of `flowVerts S ow` after deleting a separator `X`. -/
def remVerts {N : ℕ} (S : Finset (Fin N)) (ow : ℕ) (X : Finset (Option (Fin N))) :
    Finset (Fin N) :=
  S.filter (fun v => v.val ≠ ow ∧ some v ∉ X)

/-- Remaining cycle vertices of `D` in `remVerts S ow X`. -/
def remCycleVerts {N : ℕ} (S : Finset (Fin N)) (D : List (Fin N)) (ow : ℕ)
    (X : Finset (Option (Fin N))) : Finset (Fin N) :=
  (remVerts S ow X).filter (fun v => v ∈ D)

theorem mem_remVerts_iff {N : ℕ} {S : Finset (Fin N)} {ow : ℕ}
    {X : Finset (Option (Fin N))} (v : Fin N) :
    v ∈ remVerts S ow X ↔ some v ∈ flowVerts S ow \ ↑X := by
  simp [remVerts, some_mem_flowVerts_iff, and_assoc]

private theorem walk_to_remCycleVerts_of_apex_walk {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {ow : ℕ} {X : Finset (Option (Fin N))}
    {w w' : Option (Fin N)} (p : (apex G D).Walk w w')
    (hsup : ∀ x ∈ p.support, x ∈ flowVerts S ow \ ↑X)
    (y : Fin N) (hw : w = some y) (hw' : w' = none) :
    ∃ d ∈ remCycleVerts S D ow X, (restrictGraph G (remVerts S ow X)).Reachable y d := by
  induction p generalizing y with
  | nil =>
    rw [hw] at hw'
    cases hw'
  | @cons a b c hadj p ih =>
    subst hw
    have hy_rem : y ∈ remVerts S ow X :=
      (mem_remVerts_iff y).mpr (hsup (some y) (Walk.start_mem_support _))
    rcases b with _ | u
    · have hyD : y ∈ D := hadj
      exact ⟨y, Finset.mem_filter.mpr ⟨hy_rem, hyD⟩, Reachable.refl y⟩
    · have hadjG : G.Adj y u := hadj
      have hsup_p : ∀ x ∈ p.support, x ∈ flowVerts S ow \ ↑X :=
        fun x hx => hsup x (by simp [hx])
      have hu_rem : u ∈ remVerts S ow X :=
        (mem_remVerts_iff u).mpr (hsup_p (some u) (Walk.start_mem_support _))
      have hadj_rem : (restrictGraph G (remVerts S ow X)).Adj y u := ⟨hy_rem, hu_rem, hadjG⟩
      rcases ih hsup_p u rfl hw' with ⟨d, hd, hreach⟩
      exact ⟨d, hd, (SimpleGraph.Adj.reachable hadj_rem).trans hreach⟩

private theorem reachIn_apex_none_of_walk_restrict {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {ow : ℕ} {X : Finset (Option (Fin N))}
    (hX_none : (none : Option (Fin N)) ∉ X)
    {u d : Fin N} (p : (restrictGraph G (remVerts S ow X)).Walk u d)
    (hd : d ∈ remCycleVerts S D ow X) :
    ReachIn (apex G D) (flowVerts S ow \ ↑X) (some u) none := by
  induction p with
  | nil =>
    rename_i v
    rcases Finset.mem_filter.mp hd with ⟨hv_rem, hvD⟩
    have hadj_none : (apex G D).Adj (some v) none := hvD
    refine ⟨.cons hadj_none .nil, ?_⟩
    intro x hx
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact (mem_remVerts_iff v).mp hv_rem
    · exact ⟨none_mem_flowVerts S ow, hX_none⟩
  | @cons a b c hadj p ih =>
    rcases hadj with ⟨ha_rem, _, hadjG⟩
    rcases ih hd with ⟨q, hq⟩
    have hadj_apex : (apex G D).Adj (some a) (some b) := hadjG
    refine ⟨.cons hadj_apex q, ?_⟩
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (mem_remVerts_iff a).mp ha_rem
    · exact hq x hx

theorem reachIn_apex_none_iff {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {ow : ℕ} {X : Finset (Option (Fin N))}
    (hX_none : (none : Option (Fin N)) ∉ X) {y : Fin N} (hy : y ∈ remVerts S ow X) :
    ReachIn (apex G D) (flowVerts S ow \ ↑X) (some y) none ↔
      ∃ d ∈ remCycleVerts S D ow X, (restrictGraph G (remVerts S ow X)).Reachable d y := by
  let _ := hy
  constructor
  · rintro ⟨p, hp⟩
    rcases walk_to_remCycleVerts_of_apex_walk p hp y rfl rfl with ⟨d, hd, hreach⟩
    exact ⟨d, hd, hreach.symm⟩
  · rintro ⟨d, hd, hreach⟩
    rcases hreach.symm with ⟨p⟩
    exact reachIn_apex_none_of_walk_restrict hX_none p hd

open Classical in
theorem none_not_mem_extractCut {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (z : Fin N) (k ow : ℕ)
    (f : Option (Fin N) × Bool → Option (Fin N) × Bool → ℕ) :
    (none : Option (Fin N)) ∉ extractCut (apex G D) (flowVerts S ow) (some z) none k f := by
  unfold extractCut
  rw [Finset.mem_filter]
  unfold sinkCut
  rintro ⟨_, hnot, _⟩
  exact hnot Relation.ReflTransGen.refl

theorem mem_sourceSide_iff_not_reachable {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {ow : ℕ} {X : Finset (Option (Fin N))}
    (hX_none : (none : Option (Fin N)) ∉ X) (y : Fin N) :
    some y ∈ sourceSide (apex G D) (flowVerts S ow) none X ↔
      y ∈ remVerts S ow X ∧
        ¬ ∃ d ∈ remCycleVerts S D ow X, (restrictGraph G (remVerts S ow X)).Reachable d y := by
  unfold sourceSide
  rw [Set.mem_ofPred_eq]
  have hrem_iff : (some y ∈ flowVerts S ow ∧ some y ∉ X) ↔ y ∈ remVerts S ow X := by
    rw [mem_remVerts_iff]
    rfl
  by_cases hy : y ∈ remVerts S ow X
  · have hy' : some y ∈ flowVerts S ow ∧ some y ∉ X := hrem_iff.mpr hy
    rw [reachIn_apex_none_iff hX_none hy]
    exact ⟨fun h => ⟨hy, h.2.2⟩, fun h => ⟨hy'.1, hy'.2, h.2⟩⟩
  · have hnot : ¬ (some y ∈ flowVerts S ow ∧ some y ∉ X) := mt hrem_iff.mp hy
    exact ⟨fun h => absurd ⟨h.1, h.2.1⟩ hnot, fun h => absurd h.1 hy⟩

theorem mem_sourceSide_iff_of_remBfsClosed {N : ℕ} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {ow : ℕ} {X : Finset (Option (Fin N))}
    {rem_items : List ℕ}
    (hX_none : (none : Option (Fin N)) ∉ X)
    (hseed : ∀ d ∈ remCycleVerts S D ow X, d.val ∈ rem_items)
    (hsound : ∀ y : Fin N, y.val ∈ rem_items →
      ∃ d ∈ remCycleVerts S D ow X, (restrictGraph G (remVerts S ow X)).Reachable d y)
    (hclosed : ∀ u v : Fin N, u.val ∈ rem_items → v ∈ remVerts S ow X → G.Adj u v →
      v.val ∈ rem_items)
    (y : Fin N) :
    some y ∈ sourceSide (apex G D) (flowVerts S ow) none X ↔
      y ∈ remVerts S ow X ∧ y.val ∉ rem_items := by
  rw [mem_sourceSide_iff_not_reachable hX_none y]
  have hiff : (∃ d ∈ remCycleVerts S D ow X, (restrictGraph G (remVerts S ow X)).Reachable d y) ↔
      y.val ∈ rem_items := by
    constructor
    · rintro ⟨d, hd, ⟨p⟩⟩
      have hd_it : d.val ∈ rem_items := hseed d hd
      clear hd
      induction p with
      | nil => exact hd_it
      | @cons a b c hadj p ih =>
        exact ih (hclosed a b hd_it hadj.2.1 hadj.2.2)
    · exact hsound y
  rw [hiff]

end GraphMinor.Compute.Crossing
