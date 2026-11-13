module

public import GraphMinor.GM21.Section6FourTree
public import GraphMinor.GM21.Section6Cuts
import GraphMinor.GM21.Section6Disc
import GraphMinor.GM21.Section6DiscLine
import GraphMinor.GM21.Section6DiscSep
import GraphMinor.GM06.Section3Dual
import GraphMinor.GM07.Section8
import GraphMinor.GM11.Regions
import GraphMinor.GM17.CuffOrder
import GraphMinor.Surface.SurfaceGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Sort

/-!
# Graph Minors XXI, proof of (6.4): counting the edges of the tree

The end of the proof of (6.4) (page 25 of the preprint): "From (4), every vertex of $T$ has
degree at most $n$, and every path of $T$ has at most $n$ vertices. Hence
$|E(T)| \le n^n = \lambda$. But $E(T)$ is in 1-1 correspondence with the $\Sigma$-jumps, and the
result follows."

Claim (4) is used in the form of cuts (`Section6Cuts`): there is no strict chain of `n` cuts
(hypothesis `hchain`). A cut `⟨x, y, true⟩` stands for a good line with ends at the angles
`x, y`; if the points of angles `x, y` lie in the closure of one region, a line through the region
joins them, and no jump crosses it (`admissible_of_closure`).

This file proves the degree bound and the count. The paths of `T` are bounded in
`Section6FourPaths`, which also ends the proof of (6.4):

* **A region inside two jumps** (`eq_of_inner`). A region is on the inner side of at most one jump
  that it touches: two such jumps would each lie inside the other. `Section6FourPaths` uses this
  for the paths from the region `r₀` that holds the part of `bd(Σ)` outside `F*`.
* **Degrees** (`card_le_of_adj`). The jumps that a region `r` touches are at most one jump with
  `r` on its inner side, and jumps with `r` on their outer side. The latter have disjoint
  intervals of angles (`le_or_le_of_outer`). Sorted by angle, `J_1, …, J_d`, the cuts from the
  first end of `J_k` to the second end of `J_d` form a strict chain; these are the paper's good
  lines through `r`. So `d < n`, and `r` has degree at most `n`.
* **The count** (`ncard_edgeSet_le_of_isTree`). In a tree in which every vertex has degree at
  most `n` and every path from a vertex `r₀` has fewer than `n` edges, there are at most `n^k`
  vertices at distance `k` from `r₀`, so at most `n^n` vertices, and fewer edges.

The paper says "every path of $T$ has at most $n$ vertices". Claim (4) only bounds paths whose
regions are nested, that is, paths from `r₀` (see the correction to the proof of (6.4) in
`corrections/GM21.md`). Paths from `r₀` suffice for the count.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace RegionTree

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM21.DiscCut GraphMinor.GM21.Cuts

universe u v w

/-! ## Counting the vertices of a tree -/

section count

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]

omit [DecidableRel T.Adj] in
/-- In a connected graph of maximum degree at most `n`, at most `n ^ k` vertices are at distance
`k` from a vertex `v₀`: each of them has a neighbour at distance `k - 1`. -/
theorem card_dist_eq_le (hT : T.Connected) (v₀ : V) {n : ℕ}
    (hdeg : ∀ v, ∀ s : Finset V, (∀ u ∈ s, T.Adj v u) → s.card ≤ n) :
    ∀ k, #{v | T.dist v₀ v = k} ≤ n ^ k := by
  intro k
  induction k with
  | zero =>
    calc #{v | T.dist v₀ v = 0} ≤ #({v₀} : Finset V) := by
          apply Finset.card_le_card
          intro v hv
          simp only [mem_filter] at hv
          obtain ⟨p, -, hp⟩ := hT.exists_path_of_dist v₀ v
          rw [hv.2] at hp
          rw [SimpleGraph.Walk.eq_of_length_eq_zero hp]
          exact mem_singleton_self _
      _ = n ^ 0 := by simp
  | succ k ih =>
    have hpred : ∀ v, T.dist v₀ v = k + 1 → ∃ u, T.dist v₀ u = k ∧ T.Adj u v := by
      intro v hv
      obtain ⟨p, -, hp⟩ := hT.exists_path_of_dist v₀ v
      have hk : k < p.length := by omega
      have hadj : T.Adj (p.getVert k) v := by
        have := p.adj_getVert_succ hk
        rwa [show k + 1 = p.length by omega, SimpleGraph.Walk.getVert_length] at this
      refine ⟨p.getVert k, le_antisymm ?_ ?_, hadj⟩
      · calc T.dist v₀ (p.getVert k) ≤ (p.take k).length := SimpleGraph.dist_le _
          _ = k := by rw [SimpleGraph.Walk.take_length]; omega
      · obtain ⟨q, -, hq⟩ := hT.exists_path_of_dist v₀ (p.getVert k)
        have := SimpleGraph.dist_le (q.concat hadj)
        rw [SimpleGraph.Walk.length_concat, hq] at this
        omega
    choose! g hg using hpred
    set s : Finset V := {v | T.dist v₀ v = k + 1} with hs
    have hmem : ∀ v ∈ s, T.dist v₀ v = k + 1 := fun v hv => by
      simpa [hs] using hv
    calc #s ≤ n * #(s.image g) := card_le_mul_card_image s n fun u _ => by
          refine hdeg u _ fun a ha => ?_
          rw [mem_filter] at ha
          rw [← ha.2]
          exact (hg a (hmem a ha.1)).2
      _ ≤ n * #{v | T.dist v₀ v = k} := by
          refine Nat.mul_le_mul_left _ (Finset.card_le_card ?_)
          intro u hu
          obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
          simpa using (hg a (hmem a ha)).1
      _ ≤ n * n ^ k := Nat.mul_le_mul_left _ ih
      _ = n ^ (k + 1) := by ring

/-- **The count of the proof of (6.4).** A tree in which every vertex has degree at most
`n ≥ 1`, and every path from a vertex `v₀` has fewer than `n` edges (at most `n` vertices), has at
most `n ^ n` edges. -/
theorem ncard_edgeSet_le_of_isTree (hT : T.IsTree) (v₀ : V) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : ∀ v, ∀ s : Finset V, (∀ u ∈ s, T.Adj v u) → s.card ≤ n)
    (hpath : ∀ v (p : T.Walk v₀ v), p.IsPath → p.length < n) : T.edgeSet.ncard ≤ n ^ n := by
  have hlt : ∀ v, T.dist v₀ v < n := fun v => by
    obtain ⟨p, hp, hlen⟩ := hT.connected.exists_path_of_dist v₀ v
    rw [← hlen]
    exact hpath v p hp
  have hV : Fintype.card V ≤ n ^ n := by
    calc Fintype.card V = #(univ : Finset V) := rfl
      _ = ∑ k ∈ range n, #{v | T.dist v₀ v = k} :=
          card_eq_sum_card_fiberwise fun v _ => Finset.mem_range.2 (hlt v)
      _ ≤ ∑ k ∈ range n, n ^ k := sum_le_sum fun k _ => card_dist_eq_le hT.connected v₀ hdeg k
      _ ≤ ∑ _k ∈ range n, n ^ (n - 1) := sum_le_sum fun k hk =>
          Nat.pow_le_pow_right hn (by rw [Finset.mem_range] at hk; omega)
      _ = n ^ n := by
          rw [sum_const, card_range, smul_eq_mul, ← pow_succ']
          congr 1
          omega
  have hE := hT.card_edgeFinset
  rw [Set.ncard_eq_toFinset_card']
  change T.edgeFinset.card ≤ n ^ n
  omega

end count

/-! ## The tree of regions -/

section tree

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ} {a b : Fin r → ℝ} (hW : Window Γ F_star f w₀ w₁ a b)
  (hK : IsLinkage G Γ_sub)
  (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)
  (hD : GM06.IsClosedDiscSpace S) {P Q : Hypergraph α β → Set S}

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

variable (hPQ : ∀ J ∈ 𝒯, LineSplit f (UJ J) (LO J) (HI J) (P J) (Q J))

include h_pres hW hPQ

omit h_pres hPQ in
/-- An angle of the window whose point has an angle in `[x, y] ⊆ [w₀, w₁]` lies in `[x, y]`. -/
theorem mem_Icc_of_cp_mem {t x y : ℝ} (ht : t ∈ Icc w₀ w₁) (hxy : Icc x y ⊆ Icc w₀ w₁)
    (h : cp t ∈ cp '' Icc x y) : t ∈ Icc x y := by
  obtain ⟨s, hs, hst⟩ := h
  rw [angle_injOn f hW.lt_add ht (hxy hs) hst.symm]
  exact hs

/-- A point of the window on the inner side of `J` has its angle in `[lo J, hi J]`. -/
theorem mem_Icc_of_mem_left {J : Hypergraph α β} (hJ : J ∈ 𝒯) {t : ℝ} (ht : t ∈ Icc w₀ w₁)
    (htP : cp t ∈ P J) : t ∈ Icc (LO J) (HI J) := by
  have hspec := hW.jumpAngles_spec h_pres hJ
  have h : cp t ∈ P J ∩ bd S := ⟨htP, GM17.cuffPoint_mem f t⟩
  rw [(hPQ J hJ).left_inter_bd] at h
  exact mem_Icc_of_cp_mem hW ht
    (Icc_subset_Icc hspec.1 hspec.2.2.1) h

/-- A point of the window on the outer side of `J` has its angle outside `(lo J, hi J)`. -/
theorem notMem_Ioo_of_mem_right {J : Hypergraph α β} (hJ : J ∈ 𝒯) {t : ℝ} (ht : t ∈ Icc w₀ w₁)
    (htQ : cp t ∈ Q J) : t ∉ Ioo (LO J) (HI J) := by
  have hspec := hW.jumpAngles_spec h_pres hJ
  have hpi := Real.pi_pos
  have hlt := hW.lt_add
  intro htI
  have h : cp t ∈ Q J ∩ bd S := ⟨htQ, GM17.cuffPoint_mem f t⟩
  rw [(hPQ J hJ).right_inter_bd] at h
  obtain ⟨s, hs, hst⟩ := h
  rcases eq_or_lt_of_le hs.2 with hs2 | hs2
  · rw [hs2, GM17.cuffPoint_add_two_pi] at hst
    have := angle_injOn f hlt ⟨hspec.1, hspec.2.1.le.trans hspec.2.2.1⟩ ht hst
    linarith [htI.1]
  · have := GM17.cuffPoint_injOn_Ico f (LO J) ⟨by linarith [hs.1, hspec.2.1], hs2⟩
      ⟨htI.1.le, by linarith [htI.2, hspec.2.2.1, hspec.1]⟩ hst
    linarith [htI.2, hs.1]

omit hPQ in
/-- The ends of a jump lie in its line. -/
theorem cp_mem_jumpLine {J : Hypergraph α β} (hJ : J ∈ 𝒯) (hK : IsLinkage G Γ_sub) :
    cp (LO J) ∈ UJ J ∧ cp (HI J) ∈ UJ J := by
  have hl := (jumpLine_spec' h_pres hW hK hJ).1
  exact ⟨hl.left_mem, hl.right_mem⟩

include hK hdeg

/-- **A region on the inner side of two jumps that it touches.** If a region `ρ` lies on the
inner side of `J` and of `J'` and has both lines in its closure, then `J = J'`: each jump lies in
the closure of `ρ`, so on the inner side of the other, and so its angles lie inside those of the
other. -/
theorem eq_of_inner {ρ : Set S} {J J' : Hypergraph α β} (hJ : J ∈ 𝒯) (hJ' : J' ∈ 𝒯)
    (h₁ : ρ ⊆ (Q J)ᶜ) (h₂ : ρ ⊆ (Q J')ᶜ) (hU₁ : UJ J ⊆ closure ρ) (hU₂ : UJ J' ⊆ closure ρ) :
    J = J' := by
  have hsub : ∀ {K K' : Hypergraph α β}, K ∈ 𝒯 → K' ∈ 𝒯 → ρ ⊆ (Q K)ᶜ → UJ K' ⊆ closure ρ →
      LO K ≤ LO K' ∧ HI K' ≤ HI K := by
    intro K K' hK₁ hK₂ hρ hU
    have hcl : closure ρ ⊆ P K := by
      refine closure_minimal (fun z hz => ?_) (hPQ K hK₁).isClosed_left
      rw [(hPQ K hK₁).compl_right_eq] at hρ
      exact (hρ hz).1
    have hends := cp_mem_jumpLine h_pres hW hK₂ hK
    have h1 := mem_Icc_of_mem_left h_pres hW hPQ hK₁ (hW.jumpLo_mem h_pres hK₂) (hcl (hU hends.1))
    have h2 := mem_Icc_of_mem_left h_pres hW hPQ hK₁ (hW.jumpHi_mem h_pres hK₂) (hcl (hU hends.2))
    exact ⟨h1.1, h2.2⟩
  obtain ⟨a1, a2⟩ := hsub hJ hJ' h₁ hU₂
  obtain ⟨a3, a4⟩ := hsub hJ' hJ h₂ hU₁
  exact hW.jump_eq_of_angles h_pres hK hdeg hJ hJ' (le_antisymm a1 a3) (le_antisymm a4 a2)

/-- **Jumps with a region on their outer side.** If a region `ρ` lies on the outer side of two
different jumps `J, J'` and has both lines in its closure, their intervals of angles do not
overlap. -/
theorem le_or_le_of_outer {ρ : Set S} {J J' : Hypergraph α β} (hJ : J ∈ 𝒯) (hJ' : J' ∈ 𝒯)
    (hne : J ≠ J') (h₁ : ρ ⊆ (P J)ᶜ) (h₂ : ρ ⊆ (P J')ᶜ) (hU₁ : UJ J ⊆ closure ρ)
    (hU₂ : UJ J' ⊆ closure ρ) : HI J ≤ LO J' ∨ HI J' ≤ LO J := by
  -- The ends of each jump lie outside the open interval of the other.
  have hout : ∀ {K K' : Hypergraph α β}, K ∈ 𝒯 → K' ∈ 𝒯 → ρ ⊆ (P K)ᶜ → UJ K' ⊆ closure ρ →
      LO K' ∉ Ioo (LO K) (HI K) ∧ HI K' ∉ Ioo (LO K) (HI K) := by
    intro K K' hK₁ hK₂ hρ hU
    have hcl : closure ρ ⊆ Q K := by
      refine closure_minimal (fun z hz => ?_) (hPQ K hK₁).isClosed_right
      rw [(hPQ K hK₁).symm.compl_right_eq] at hρ
      exact (hρ hz).1
    have hends := cp_mem_jumpLine h_pres hW hK₂ hK
    exact ⟨notMem_Ioo_of_mem_right h_pres hW hPQ hK₁ (hW.jumpLo_mem h_pres hK₂) (hcl (hU hends.1)),
      notMem_Ioo_of_mem_right h_pres hW hPQ hK₁ (hW.jumpHi_mem h_pres hK₂) (hcl (hU hends.2))⟩
  obtain ⟨o1, o2⟩ := hout hJ hJ' h₁ hU₂
  obtain ⟨o3, o4⟩ := hout hJ' hJ h₂ hU₁
  have l1 := (hW.jumpAngles_spec h_pres hJ).2.1
  have l2 := (hW.jumpAngles_spec h_pres hJ').2.1
  simp only [mem_Ioo, not_and, not_lt] at o1 o2 o3 o4
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2⟩ := hcon
  have e1 : LO J = LO J' := by
    rcases lt_trichotomy (LO J) (LO J') with h | h | h
    · linarith [o1 h]
    · exact h
    · linarith [o3 h]
  have e2 : HI J = HI J' := le_antisymm (o2 c2) (o4 c1)
  exact hne (hW.jump_eq_of_angles h_pres hK hdeg hJ hJ' e1 e2)

include hD

omit hdeg in
/-- **A good line through a region.** If the points of angles `x < y` are vertices of `Γ` in the
closure of a region `ρ`, then no jump crosses the cut `⟨x, y, true⟩`: a line through `ρ` joins the
two points (`DiscLine.exists_line_in_region`), and a jump that crossed the cut would meet it. -/
theorem admissible_of_closure {ρ : Set S} (hρ : ρ ∈ Γ.R) {x y : ℝ} (hx : x ∈ POS) (hy : y ∈ POS)
    (hxy : x < y) (hxρ : cp x ∈ closure ρ) (hyρ : cp y ∈ closure ρ) :
    Admissible LO HI 𝒯 POS ⟨x, y, true⟩ := by
  have : T2Space S := GM06.t2Space_of_isClosedDiscSpace hD
  have hlt := hW.lt_add
  have hpi := Real.pi_pos
  have hne : cp x ≠ cp y := fun h => hxy.ne (angle_injOn f hlt hx.1 hy.1 h)
  obtain ⟨F, hF, hFρ⟩ := DiscLine.exists_line_in_region hD h_pres.is_proper_drawing hρ hx.2 hy.2
    hne hxρ hyρ
  -- A common point of `F` and the line of a jump is an end of `F`, at an end of the jump.
  have hmeet : ∀ J ∈ 𝒯, ∀ z ∈ F ∩ UJ J, z = cp x ∨ z = cp y := by
    intro J _ z ⟨hzF, hzJ⟩
    rcases hFρ hzF with hz | hz
    · exact hz
    · exact (GM11.region_subset hρ hz.1 (jumpLine_subset_U J hzJ)).elim
  have hend : ∀ J ∈ 𝒯, ∀ {t : ℝ}, t ∈ POS → cp t ∈ UJ J → t = LO J ∨ t = HI J := by
    intro J hJ t ht htJ
    have h : cp t ∈ UJ J ∩ bd S := ⟨htJ, GM17.cuffPoint_mem f t⟩
    rw [(jumpLine_spec' h_pres hW hK hJ).2] at h
    rcases h with h | h
    · exact Or.inl (angle_injOn f hlt ht.1 (hW.jumpLo_mem h_pres hJ) h)
    · exact Or.inr (angle_injOn f hlt ht.1 (hW.jumpHi_mem h_pres hJ) (mem_singleton_iff.mp h))
  refine ⟨hx, hy, hxy, fun J hJ => ⟨?_, ?_⟩⟩
  · rintro ⟨h1, h2, h3⟩
    have hspec := hW.jumpAngles_spec h_pres hJ
    have hl := (hPQ J hJ).isLine
    obtain ⟨z, hzF, hzJ⟩ := GM06.discCrossing_of_isClosedDiscSpace hD hF.isCompact hl.isCompact
      (GM07.IsLineWithEnds.isConnected hF) (GM07.IsLineWithEnds.isConnected hl) hF.left_mem
      hF.right_mem hl.left_mem hl.right_mem
      (pairsCrossOn_of_angles f h1 h2 h3 (by linarith [hspec.2.2.1, hx.1.1]))
    rcases hmeet J hJ z ⟨hzF, hzJ⟩ with rfl | rfl
    · rcases hend J hJ hx hzJ with h | h <;> linarith
    · rcases hend J hJ hy hzJ with h | h <;> linarith
  · rintro ⟨h1, h2, h3⟩
    have hspec := hW.jumpAngles_spec h_pres hJ
    have hl := (hPQ J hJ).isLine
    obtain ⟨z, hzJ, hzF⟩ := GM06.discCrossing_of_isClosedDiscSpace hD hl.isCompact hF.isCompact
      (GM07.IsLineWithEnds.isConnected hl) (GM07.IsLineWithEnds.isConnected hF) hl.left_mem
      hl.right_mem hF.left_mem hF.right_mem
      (pairsCrossOn_of_angles f h1 h2 h3 (by linarith [hspec.1, hy.1.2]))
    rcases hmeet J hJ z ⟨hzF, hzJ⟩ with rfl | rfl
    · rcases hend J hJ hx hzJ with h | h <;> linarith
    · rcases hend J hJ hy hzJ with h | h <;> linarith

omit hdeg in
/-- The cut of a jump `J` whose line lies in the closure of a region is admissible. -/
theorem admissible_jump {ρ : Set S} (hρ : ρ ∈ Γ.R) {J : Hypergraph α β} (hJ : J ∈ 𝒯)
    (hU : UJ J ⊆ closure ρ) : Admissible LO HI 𝒯 POS ⟨LO J, HI J, true⟩ := by
  have hspec := hW.jumpAngles_spec h_pres hJ
  have hends := cp_mem_jumpLine h_pres hW hJ hK
  exact admissible_of_closure h_pres hW hK hD hPQ hρ ⟨hW.jumpLo_mem h_pres hJ, hspec.2.2.2.1⟩
    ⟨hW.jumpHi_mem h_pres hJ, hspec.2.2.2.2.1⟩ hspec.2.1 (hU hends.1) (hU hends.2)

omit h_pres hW hPQ hK hdeg hD in
/-- Nested intervals give nested cuts. -/
theorem nested_of_le {x y x' y' : ℝ} (hx : x ≤ x') (hy : y' ≤ y) :
    Nested LO HI 𝒯 ⟨x, y, true⟩ ⟨x', y', true⟩ :=
  ⟨hx, hy, fun _J hJ => ⟨hJ.1, hx.trans hJ.2.1, hJ.2.2.1.trans hy, Or.inl rfl⟩⟩

/-- **A region with `n` jumps on their outer side gives a strict chain** of `n` cuts. -/
theorem card_outer_lt {n : ℕ} (hchain : ∀ d : Fin n → Cut, ¬ IsStrictChain LO HI 𝒯 POS d)
    {ρ : Set S} (hρ : ρ ∈ Γ.R) (s : Finset (Hypergraph α β))
    (hs : ∀ J ∈ s, J ∈ 𝒯 ∧ ρ ⊆ (P J)ᶜ ∧ UJ J ⊆ closure ρ) : s.card < n := by
  classical
  by_contra hcon
  push Not at hcon
  -- The first ends of the jumps of `s` are different.
  have hinj : Set.InjOn LO (s : Set (Hypergraph α β)) := by
    intro J hJ J' hJ' heq
    by_contra hne
    have l := (hW.jumpAngles_spec h_pres (hs J hJ).1).2.1
    rcases le_or_le_of_outer h_pres hW hK hdeg hPQ (hs J hJ).1 (hs J' hJ').1 hne (hs J hJ).2.1
      (hs J' hJ').2.1 (hs J hJ).2.2 (hs J' hJ').2.2 with h | h
    · linarith
    · have l' := (hW.jumpAngles_spec h_pres (hs J' hJ').1).2.1
      linarith
  set L := s.image LO with hL
  have hLcard : L.card = s.card := Finset.card_image_of_injOn hinj
  set e := L.orderEmbOfFin hLcard with he
  have hn : 0 < n := by
    by_contra h0
    push Not at h0
    have h0' : n = 0 := by omega
    subst h0'
    exact hchain Fin.elim0 ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  -- The jump with first end `e k`.
  have hex : ∀ k : Fin s.card, ∃ J ∈ s, LO J = e k := fun k =>
    Finset.mem_image.1 (L.orderEmbOfFin_mem hLcard k)
  choose Jk hJks hJk using hex
  have hmono : ∀ {i j : Fin s.card}, i < j → LO (Jk i) < LO (Jk j) := by
    intro i j hij
    rw [hJk, hJk]
    exact e.strictMono hij
  have hsep : ∀ {i j : Fin s.card}, i < j → HI (Jk i) ≤ LO (Jk j) := by
    intro i j hij
    have hlt := hmono hij
    have hne : Jk i ≠ Jk j := fun h => (h ▸ hlt).false
    rcases le_or_le_of_outer h_pres hW hK hdeg hPQ (hs _ (hJks i)).1 (hs _ (hJks j)).1 hne
      (hs _ (hJks i)).2.1 (hs _ (hJks j)).2.1 (hs _ (hJks i)).2.2 (hs _ (hJks j)).2.2 with h | h
    · exact h
    · have := (hW.jumpAngles_spec h_pres (hs _ (hJks j)).1).2.1
      linarith
  set last : Fin s.card := ⟨n - 1, by omega⟩ with hlast
  set y := HI (Jk last) with hy
  let idx : Fin n → Fin s.card := fun k => ⟨k.1, by omega⟩
  let d : Fin n → Cut := fun k => ⟨LO (Jk (idx k)), y, true⟩
  have hspec := fun k => hW.jumpAngles_spec h_pres (hs _ (hJks k)).1
  have hends := fun k => cp_mem_jumpLine h_pres hW (hs _ (hJks k)).1 hK
  have hhi_le : ∀ k : Fin n, HI (Jk (idx k)) ≤ y := by
    intro k
    rcases eq_or_lt_of_le (show (idx k).1 ≤ last.1 by simp [idx, hlast]; omega) with h | h
    · rw [show idx k = last from Fin.ext h]
    · exact (hsep (show idx k < last from h)).trans (hspec last).2.1.le
  apply hchain d
  refine ⟨fun k => ?_, fun i j hij => ?_, fun i h => ?_⟩
  · refine admissible_of_closure h_pres hW hK hD hPQ hρ
      ⟨hW.jumpLo_mem h_pres (hs _ (hJks _)).1, (hspec _).2.2.2.1⟩
      ⟨hW.jumpHi_mem h_pres (hs _ (hJks _)).1, (hspec _).2.2.2.2.1⟩
      (lt_of_lt_of_le (hspec _).2.1 (hhi_le k)) ((hs _ (hJks _)).2.2 (hends _).1)
      ((hs _ (hJks _)).2.2 (hends _).2)
  · exact nested_of_le (hmono (show idx i < idx j from hij)).le le_rfl
  · intro hsub
    have hin : Jk (idx i) ∈ insideSet LO HI 𝒯 (d i) :=
      ⟨(hs _ (hJks _)).1, le_rfl, hhi_le i, Or.inl rfl⟩
    have h2 := (hsub hin).2.1
    have h3 := hmono (show idx i < idx ⟨i.1 + 1, h⟩ from Fin.mk_lt_mk.2 (by simp))
    exact absurd h2 (not_le.2 h3)

/-- **Every vertex of `T` has degree at most `n`.** The jumps across which a region touches its
neighbours are different for different neighbours; at most one has the region on its inner side
(`eq_of_inner`), and fewer than `n` have it on their outer side (`card_outer_lt`). -/
theorem card_le_of_adj (hPQh : ∀ J ∈ 𝒯, Halves (UJ J) (P J) (Q J)) {n : ℕ}
    (hchain : ∀ d : Fin n → Cut, ¬ IsStrictChain LO HI 𝒯 POS d) (ρ : Γ.R) (s : Finset Γ.R)
    (hs : ∀ σ ∈ s, (touchGraph Γ).Adj ρ σ) : s.card ≤ n := by
  classical
  have hex : ∀ σ ∈ s, ∃ J ∈ 𝒯, Across Γ ιE P Q J ρ.1 σ.1 := fun σ hσ =>
    exists_across_of_touch h_pres hK hdeg hD hPQh ρ.2 σ.2 (hs σ hσ)
  choose! j hj𝒯 hjacr using hex
  have hinj : Set.InjOn j (s : Set Γ.R) := by
    intro σ hσ σ' hσ' heq
    have := across_eq h_pres hD hPQh (hj𝒯 σ hσ) ρ.2 σ.2 ρ.2 σ'.2 (hjacr σ hσ)
      (heq ▸ hjacr σ' hσ')
    rcases Sym2.eq_iff.1 this with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact Subtype.ext h
    · exact Subtype.ext (h2.trans h1)
  set t := s.image j with ht
  have htcard : t.card = s.card := Finset.card_image_of_injOn hinj
  have hmem : ∀ J ∈ t, J ∈ 𝒯 ∧ UJ J ⊆ closure ρ.1 ∧ (ρ.1 ⊆ (Q J)ᶜ ∨ ρ.1 ⊆ (P J)ᶜ) := by
    intro J hJ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hJ
    obtain ⟨hside, h1, -⟩ := hjacr σ hσ
    exact ⟨hj𝒯 σ hσ, h1, hside.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
  set tin := t.filter fun J => ρ.1 ⊆ (Q J)ᶜ
  set tout := t.filter fun J => ¬ ρ.1 ⊆ (Q J)ᶜ
  have hin : tin.card ≤ 1 := by
    refine Finset.card_le_one.2 fun J hJ J' hJ' => ?_
    rw [Finset.mem_filter] at hJ hJ'
    exact eq_of_inner h_pres hW hK hdeg hPQ (hmem J hJ.1).1 (hmem J' hJ'.1).1 hJ.2 hJ'.2
      (hmem J hJ.1).2.1 (hmem J' hJ'.1).2.1
  have hout : tout.card < n := by
    refine card_outer_lt h_pres hW hK hdeg hD hPQ hchain ρ.2 tout fun J hJ => ?_
    rw [Finset.mem_filter] at hJ
    obtain ⟨h1, h2, h3⟩ := hmem J hJ.1
    exact ⟨h1, h3.resolve_left hJ.2, h2⟩
  have hsum : tin.card + tout.card = t.card := Finset.card_filter_add_card_filter_not _
  omega

end tree

end RegionTree
end GM21
end GraphMinor
