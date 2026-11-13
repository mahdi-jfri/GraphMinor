module

public import GraphMinor.GM21.Section6ClaimFourGap
import GraphMinor.Surface.CutIArc

/-!
# Graph Minors XXI, (6.3), the last step: the bound for one side

The last step of the proof of (6.3) cuts `Σ` along one more line `F` and bounds the jumps on each
side. Here are the three facts it uses.
* `side_jumps_le`: a side of smaller type has at most `λ(p + 4q, q, r + 1)` jumps. This is the bound
  of claim (4) for one side (`ClaimFour.side_jumps_le_of_supports`, `side_jumps_le_of_mid`,
  `side_jumps_le_of_gap`).
* `sigmaJumps_side_eq_empty`: a side that contains no edge of `Γ` has no jumps, since a jump has an
  edge.
* `hasType_of_isClosedDisc`: a closed disc has type `(0, 1)`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Topology Function GraphMinor.Surface GraphMinor.GM21.Induction GraphMinor.GM21.Side
  GraphMinor.GM21.Supports GraphMinor.GM21.Split GraphMinor.GM19 Hypergraph

universe u v

/-- A closed disc has type `(0, 1)`. -/
theorem hasType_of_isClosedDisc {S : Type} [TopologicalSpace S] {E : Set S}
    (hE : IsClosedDisc E) : HasType E 0 1 := by
  obtain ⟨φ⟩ := hE
  obtain ⟨d⟩ := nonempty_disc_homeo
  exact ⟨0, 0, rfl, ⟨φ.symm.trans d.symm⟩⟩

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S] [T2Space S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
  {r' : ℕ} {F_star : Fin r' → Set S} {H : Fin r' → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {L : Hypergraph α β} {S₁ S₂ F : Set S} {a b : S}

/-- **The bound for one side** (Graph Minors XXI, proof of (6.3), claim (4), page 29 of the
preprint). A side `Σ₁` of a separating line whose type comes before the type of `Σ` has at most
`λ(p + 4q, q, r + 1)` jumps. -/
theorem side_jumps_le (hS : IsSurface S) {n c p q r lam : ℕ}
    (hlam : BoundBelow.{u, v} n c (p + 4 * q) q (r + 1) lam) (hG : G.IsGraph)
    (hr : r' ≤ r) (hd : PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    (h : IsSideOfLine Γ S₁ S₂ F a b) [ConnectedSpace S₁] {n₁ c₁ : ℕ} (hT₁ : HasType S₁ n₁ c₁)
    (hlt : TypeLt n₁ c₁ n c) :
    (sigmaJumps (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁)
      (ιV ∘ Subtype.val)).encard ≤ lam := by
  classical
  obtain ⟨qf, hP, hqf, -⟩ := hd
  by_cases hboth : ∃ j₀, a ∈ F_star j₀ ∧ b ∈ F_star j₀
  swap
  · exact ClaimFour.side_jumps_le_of_supports hlam hP hqf hr hG hL hLp h hT₁ hlt fun j hne =>
      ClaimFour.isSupport_inter_side h (hP.supports_isSupport j) (not_exists.mp hboth j) hne
  obtain ⟨j₀, haj, hbj⟩ := hboth
  obtain ⟨e₀, e₁, hFe⟩ := hP.supports_isSupport j₀
  obtain ⟨C', hC', hFC'⟩ := exists_cuff_of_supportHasEnds hFe
  set f := cuffHomeo hS hC'
  obtain ⟨t₀, -, t₁, ⟨-, hlt'⟩, hends, hFeq, -⟩ := support_eq_cuffPoint_Icc hS hC' f hFe hFC'
  have hFends := ends_mem_of_supportHasEnds hFe
  have ht₀V : cuffPoint f t₀ ∈ Γ.V := by
    rcases hends with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h']
    · exact hFends.2.2.1.1
    · exact hFends.2.2.2.1.1
  have ht₁V : cuffPoint f t₁ ∈ Γ.V := by
    rcases hends with ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [h']
    · exact hFends.2.2.2.1.1
    · exact hFends.2.2.1.1
  obtain ⟨xa, hxa, hxa_eq⟩ := hFeq ▸ haj
  obtain ⟨xb, hxb, hxb_eq⟩ := hFeq ▸ hbj
  have hne : xa ≠ xb := fun h' => h.proper.ne (hxa_eq.symm.trans (h' ▸ hxb_eq))
  obtain ⟨x, y, ht₀x, hxy, hyt₁, hab⟩ : ∃ x y, t₀ ≤ x ∧ x < y ∧ y ≤ t₁ ∧
      ({cuffPoint f x, cuffPoint f y} : Set S) = {a, b} := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨xa, xb, hxa.1, hlt, hxb.2, by rw [hxa_eq, hxb_eq]⟩
    · exact ⟨xb, xa, hxb.1, hlt, hxa.2, by rw [hxa_eq, hxb_eq, pair_comm]⟩
  have hpi := Real.pi_pos
  have hy2 : y < x + 2 * Real.pi := by linarith
  have haC' : a ∈ C' := hFC' haj
  rcases Gap.arcs_on_sides hS h hC' haC' f hxy hy2 hab with ⟨hM₁, hO₁⟩ | ⟨hM₁, hO₁⟩
  · exact ClaimFour.side_jumps_le_of_mid hS hlam hP hqf hr hG hL hLp h hT₁ hlt hC' f j₀ ht₀x hxy
      hyt₁ hlt' hFeq hab hM₁ hO₁
  · exact ClaimFour.side_jumps_le_of_gap hS hlam hP hqf hr hG hL hLp h hT₁ hlt hC' f j₀ ht₀x hxy
      hyt₁ hlt' ht₀V ht₁V hFeq hab hM₁ hO₁

/-- A side that contains no edge of `Γ` has no jumps: a jump joins two different vertices, so it
has an edge. -/
theorem sigmaJumps_side_eq_empty (hiso : IsDrawingIso Γ Γ_sub ιV ιE) (h₁ : IsClosed S₁)
    (hE : ∀ e ∈ Γ.E, ¬ e ⊆ S₁) :
    sigmaJumps (sideDrawing Γ h₁) (sideSub Γ Γ_sub ιV ιE S₁) (ιV ∘ Subtype.val) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun J hJ => ?_
  obtain ⟨hJle, hJp, u, hu, v, hv, huv, hterm, -⟩ := hJ
  have huV : u.1 ∈ Γ.V := by
    have := hu.1
    rw [sideDrawing_V] at this
    exact this
  have hvV : v.1 ∈ Γ.V := by
    have := hv.1
    rw [sideDrawing_V] at this
    exact this
  have hne : ιV u.1 ≠ ιV v.1 := fun h' => huv (Subtype.ext (hiso.ιV_injOn huV hvV h'))
  have ha : ιV u.1 ∈ J.vertexSet := (show ιV u.1 ∈ terminals J from hterm ▸ Or.inl rfl).1
  have hb : ιV v.1 ∈ J.vertexSet := (show ιV v.1 ∈ terminals J from hterm ▸ Or.inr rfl).1
  obtain ⟨p⟩ := hJp.2.2.1 _ ha _ hb
  obtain ⟨w, hadj, -, -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne p
  obtain ⟨-, f, hf, -⟩ := hadj
  have hfJ := hJle.edgeSet_subset (J.edge_mem_of_inc hf)
  obtain ⟨⟨e, ⟨he, heS⟩, -⟩, -⟩ := hfJ
  exact hE e he heS

end LastStep
end GM21
end GraphMinor
