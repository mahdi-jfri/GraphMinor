module

public import GraphMinor.GM21.Section6FourCount
import GraphMinor.GM21.Section6DiscSep
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM11.Regions
import GraphMinor.GM17.CuffOrder
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Graph Minors XXI, proof of (6.4): paths of the tree and the bound on the jumps

This file ends the proof of (6.4) (page 25 of the preprint): "every path of $T$ has at most
$n$ vertices. Hence $|E(T)| \le n^n = \lambda$. But $E(T)$ is in 1-1 correspondence with the
$\Sigma$-jumps, and the result follows."

* `exists_root`: the region `r₀` that holds the part of `bd(Σ)` outside the window of angles. It
  lies on the outer side of every jump.
* `length_lt_of_isPath`: a path of `T` from `r₀` has fewer than `n` edges. Along the path each
  step crosses a jump from its outer side to its inner side, the next jump lies inside it, and the
  cuts of these jumps form a strict chain (Claim (4)).
* `ncard_jumpSet_le`: at most `n ^ n` jumps, from the count of `Section6FourCount` and the
  bijection between the jumps and the edges of `T`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace RegionTree

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM21.DiscCut GraphMinor.GM21.Cuts

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ} {a b : Fin r → ℝ} (hW : Window Γ F_star f w₀ w₁ a b)
  (hK : IsLinkage G Γ_sub)
  (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)
  (hD : GM06.IsClosedDiscSpace S)

set_option hygiene false in
local notation "𝒯" => jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))
set_option hygiene false in
local notation "LO" => jumpLo f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "HI" => jumpHi f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "POS" => {t : ℝ | t ∈ Icc w₀ w₁ ∧ GM19.cuffPoint f t ∈ Γ.V}
set_option hygiene false in
local notation "cp" => GM19.cuffPoint f
set_option hygiene false in
local notation "UJ" => LastStep.jumpLine Γ ιE

section paths

variable {P Q : Hypergraph α β → Set S}
  (hPQ : ∀ J ∈ 𝒯, LineSplit f (UJ J) (LO J) (HI J) (P J) (Q J))

include h_pres hW hPQ

/-- **The region outside the window.** The point of angle halfway between `w₁` and `w₀ + 2π` is
not in `U(Γ)`, and its region lies on the outer side of every jump, since the inner side of a jump
meets `bd(Σ)` only in angles of the window. -/
theorem exists_root : ∃ ρ₀ ∈ Γ.R, ∀ J ∈ 𝒯, ρ₀ ⊆ (P J)ᶜ := by
  have hlt := hW.lt_add
  have hpi := Real.pi_pos
  set t₀ := (max w₀ w₁ + (w₀ + 2 * Real.pi)) / 2 with ht₀
  have hm : max w₀ w₁ < w₀ + 2 * Real.pi := max_lt (by linarith) hlt
  have h1 : max w₀ w₁ < t₀ := by rw [ht₀]; linarith
  have h2 : t₀ < w₀ + 2 * Real.pi := by rw [ht₀]; linarith
  have h1' := (le_max_left w₀ w₁).trans_lt h1
  have h1'' := (le_max_right w₀ w₁).trans_lt h1
  -- An angle of the window with the same point as `t₀` is `t₀`.
  have hinj : ∀ {s : ℝ}, s ∈ Icc w₀ w₁ → cp s = cp t₀ → False := by
    intro s hs heq
    have := GM17.cuffPoint_injOn_Ico f w₀ ⟨hs.1, by linarith [hs.2]⟩ ⟨h1'.le, h2⟩ heq
    linarith [hs.2]
  have hnV : cp t₀ ∉ Γ.V := by
    intro h
    obtain ⟨s, hs, heq⟩ := hW.exists_angle' h_pres ⟨h, GM17.cuffPoint_mem f t₀⟩
    exact hinj hs heq
  have hnU : cp t₀ ∉ Γ.U := fun h => hnV (h_pres.is_proper_drawing ⟨GM17.cuffPoint_mem f t₀, h⟩)
  obtain ⟨ρ₀, hρ₀, hz⟩ := GM11.exists_region_of_notMem hnU
  refine ⟨ρ₀, hρ₀, fun J hJ => ?_⟩
  have hspec := hW.jumpAngles_spec h_pres hJ
  have hnP : cp t₀ ∉ P J := by
    intro hP
    have h : cp t₀ ∈ P J ∩ bd S := ⟨hP, GM17.cuffPoint_mem f t₀⟩
    rw [(hPQ J hJ).left_inter_bd] at h
    obtain ⟨s, hs, heq⟩ := h
    exact hinj ⟨hspec.1.trans hs.1, hs.2.trans hspec.2.2.1⟩ heq
  exact (hPQ J hJ).toHalves.symm.region_subset_right_of_mem (jumpLine_subset_U J) hρ₀ hz hnP

include hK hdeg hD

/-- **A path of `T` from the region outside the window has fewer than `n` edges.** -/
theorem length_lt_of_isPath {n : ℕ} (hchain : ∀ d : Fin n → Cut, ¬ IsStrictChain LO HI 𝒯 POS d)
    {ρ₀ : Γ.R} (hroot : ∀ J ∈ 𝒯, ρ₀.1 ⊆ (P J)ᶜ) {v : Γ.R} (p : (touchGraph Γ).Walk ρ₀ v)
    (hp : p.IsPath) : p.length < n := by
  classical
  have hPQh : ∀ J ∈ 𝒯, Halves (UJ J) (P J) (Q J) := fun J hJ => (hPQ J hJ).toHalves
  by_contra hcon
  push Not at hcon
  set m := p.length with hm
  set gv : ℕ → Γ.R := p.getVert with hgv
  -- The jump `J i` across the `i`th edge of the path.
  have hex : ∀ i : ℕ, ∃ J : Hypergraph α β, i < m → J ∈ 𝒯 ∧ Across Γ ιE P Q J (gv i).1 (gv (i + 1)).1 := by
    intro i
    by_cases hi : i < m
    · obtain ⟨J, hJ, h⟩ := exists_across_of_touch h_pres hK hdeg hD hPQh (gv i).2 (gv (i + 1)).2
        (p.adj_getVert_succ hi)
      exact ⟨J, fun _ => ⟨hJ, h⟩⟩
    · exact ⟨Γ_sub, fun h => (hi h).elim⟩
  choose J hJ using hex
  have hvinj : ∀ {i j : ℕ}, i ≤ m → j ≤ m → gv i = gv j → i = j := fun hi hj h =>
    hp.getVert_injOn hi hj h
  -- Two consecutive jumps of the path are different.
  have hne : ∀ i, i + 1 < m → J i ≠ J (i + 1) := by
    intro i hi heq
    have h1 := (hJ i (by omega)).2
    have h2 := (hJ (i + 1) hi).2
    rw [heq] at h1
    have := sym2_eq_of_val (across_eq h_pres hD hPQh (hJ (i + 1) hi).1 (gv i).2 (gv (i + 1)).2
      (gv (i + 1)).2 (gv (i + 2)).2 h1 h2)
    rcases Sym2.eq_iff.1 this with ⟨h3, -⟩ | ⟨h3, -⟩
    · have := hvinj (by omega) (by omega) h3
      omega
    · have := hvinj (by omega) (by omega) h3
      omega
  -- Each step goes from the outer side to the inner side of its jump.
  have hstep : ∀ i, i < m → (gv i).1 ⊆ (P (J i))ᶜ → (gv (i + 1)).1 ⊆ (Q (J i))ᶜ := by
    intro i hi h
    rcases (hJ i hi).2.1 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ((hPQh _ (hJ i hi).1).region_not_subset_both (gv i).2 h1 h).elim
    · exact h2
  have hout : ∀ i, i < m → (gv i).1 ⊆ (P (J i))ᶜ := by
    intro i
    induction i with
    | zero =>
      intro h0
      have : gv 0 = ρ₀ := p.getVert_zero
      rw [this]
      exact hroot _ (hJ 0 h0).1
    | succ i ih =>
      intro hi
      have hin := hstep i (by omega) (ih (by omega))
      have hacr := (hJ i (by omega)).2
      have hacr' := (hJ (i + 1) hi).2
      rcases hacr'.1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact (hne i hi (eq_of_inner h_pres hW hK hdeg hPQ (hJ i (by omega)).1 (hJ (i + 1) hi).1
          hin h1 hacr.2.2 hacr'.2.1)).elim
      · exact h1
  -- The next jump lies inside the jump before.
  have hnext : ∀ i, i + 1 < m → LO (J i) ≤ LO (J (i + 1)) ∧ HI (J (i + 1)) ≤ HI (J i) := by
    intro i hi
    have hin := hstep i (by omega) (hout i (by omega))
    have hs := hPQ (J i) (hJ i (by omega)).1
    have hcl : closure (gv (i + 1)).1 ⊆ P (J i) := by
      refine closure_minimal (fun z hz => ?_) hs.isClosed_left
      rw [hs.compl_right_eq] at hin
      exact (hin hz).1
    have hJ' := (hJ (i + 1) hi).1
    have hends := cp_mem_jumpLine h_pres hW hJ' hK
    have hU := (hJ (i + 1) hi).2.2.1
    have k1 := mem_Icc_of_mem_left h_pres hW hPQ (hJ i (by omega)).1 (hW.jumpLo_mem h_pres hJ')
      (hcl (hU hends.1))
    have k2 := mem_Icc_of_mem_left h_pres hW hPQ (hJ i (by omega)).1 (hW.jumpHi_mem h_pres hJ')
      (hcl (hU hends.2))
    exact ⟨k1.1, k2.2⟩
  have hnest : ∀ i j, i ≤ j → j < m → LO (J i) ≤ LO (J j) ∧ HI (J j) ≤ HI (J i) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ => ⟨le_rfl, le_rfl⟩
    | succ j _ ih =>
      intro hj
      obtain ⟨a1, a2⟩ := ih (by omega)
      obtain ⟨a3, a4⟩ := hnext j hj
      exact ⟨a1.trans a3, a4.trans a2⟩
  -- The cuts of `J 0, …, J (n - 1)` form a strict chain.
  let d : Fin n → Cut := fun k => ⟨LO (J k), HI (J k), true⟩
  apply hchain d
  refine ⟨fun k => ?_, fun i j hij => ?_, fun i h => ?_⟩
  · have hk : k.1 < m := by omega
    exact admissible_jump h_pres hW hK hD hPQ (gv k).2 (hJ k hk).1 (hJ k hk).2.2.1
  · obtain ⟨a1, a2⟩ := hnest i j hij.le (by omega)
    exact nested_of_le a1 a2
  · intro hsub
    have hi : i.1 < m := by omega
    have hin : J i ∈ insideSet LO HI 𝒯 (d i) := ⟨(hJ i hi).1, le_rfl, le_rfl, Or.inl rfl⟩
    obtain ⟨-, b1, b2, -⟩ := hsub hin
    obtain ⟨a1, a2⟩ := hnext i (by omega)
    exact hne i (by omega) (hW.jump_eq_of_angles h_pres hK hdeg (hJ i hi).1 (hJ (i + 1) (by omega)).1
      (le_antisymm a1 b1) (le_antisymm b2 a2))

end paths

include h_pres hW hK hdeg hD

/-- **The jumps of the proof of (6.4)**, counted through the tree of regions. If there is no strict
chain of `n ≥ 1` cuts (Claim (4)), there are at most `n ^ n` jumps: `T` is a tree, its vertices
have degree at most `n`, its paths from the region outside the window have fewer than `n` edges,
and its edges correspond to the jumps. -/
theorem ncard_jumpSet_le {n : ℕ} (hn : 1 ≤ n)
    (hchain : ∀ d : Fin n → Cut, ¬ IsStrictChain LO HI 𝒯 POS d) : Set.ncard 𝒯 ≤ n ^ n := by
  classical
  obtain ⟨P, Q, hPQ⟩ := exists_jumpSplits h_pres hW hK hD
  have hPQh : ∀ J ∈ 𝒯, Halves (UJ J) (P J) (Q J) := fun J hJ => (hPQ J hJ).toHalves
  obtain ⟨ρ₀, hρ₀, hroot⟩ := exists_root h_pres hW hPQ
  have : Nonempty Γ.R := ⟨⟨ρ₀, hρ₀⟩⟩
  let _ : Fintype Γ.R := (GM06.disc_finite_R hD Γ h_pres.is_proper_drawing).fintype
  rw [ncard_jumpSet_eq_ncard_edgeSet h_pres hK hdeg hD hPQh]
  exact ncard_edgeSet_le_of_isTree (touchGraph_isTree h_pres hK hdeg hD hPQh) ⟨ρ₀, hρ₀⟩ hn
    (fun ρ s hs => card_le_of_adj h_pres hW hK hdeg hD hPQ hPQh hchain ρ s hs)
    (fun _ p hp => length_lt_of_isPath h_pres hW hK hdeg hD hPQ hchain hroot p hp)

end RegionTree
end GM21
end GraphMinor
