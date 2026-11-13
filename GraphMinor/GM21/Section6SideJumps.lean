module

public import GraphMinor.GM21.Section6RestrictPres
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, Section 6: the jumps on the two sides of a line

Let `F` be a proper line in `Σ` with ends `a, b ∈ V(Γ)` and no other point in `U(Γ)`, with sides
`Σ₁, Σ₂` (`IsSideOfLine`). The proofs of (6.6), (6.7) and of claim (4) of (6.3) in
*Graph Minors XXI* (pages 28–30 of the preprint) end with "every $\Sigma$-jump belongs to one of
$\Delta_1, \Delta_2$" or "there are $\le \lambda(p + 2q, q, r + 1)$ $\Sigma_i$-jumps in $\Gamma_i$
for $i = 1, 2$, and hence $\le 2\lambda(p + 2q, q, r + 1) \le \lambda$ $\Sigma$-jumps in
$\Gamma$". This file proves it.

A `Σ`-jump `J` lies on one side: if two edges of `J` lay on different sides, then, since `J` is
connected, some vertex of `J` would be an end of an edge on each side
(`exists_inc_of_reachable`). That vertex lies in `Σ₁ ∩ Σ₂ = F`, so it is `a` or `b`, a vertex of
`Γ` in `bd(Σ)`. It has degree at least 2 in `J`, so it is not an end of `J`, which a jump forbids.
A jump on the side `Σ₁` is a `Σ₁`-jump of `Γ ∩ Σ₁` (`isSigmaJump_side`). So the number of
`Σ`-jumps is at most the sum of the numbers of jumps on the two sides
(`encard_sigmaJumps_le_side`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Topology Function GraphMinor.Surface Hypergraph

universe u v w

variable {α : Type u} {β : Type v}

/-- **Two classes of edges in a connected graph meet at a vertex.** If `J` is connected, `e₁` has
the property `P` and `e₂` does not, and both have an end, then some vertex is an end of an edge
with `P` and of an edge without `P`. Otherwise the set of ends of edges with `P` would be closed
under steps of the skeleton, and a walk from an end of `e₁` to an end of `e₂` would stay in it. -/
theorem exists_inc_of_reachable {J : Hypergraph α β} (P : β → Prop)
    (hconn : ∀ x ∈ J.vertexSet, ∀ y ∈ J.vertexSet, J.skeleton.Reachable x y) {e₁ e₂ : β}
    {x y : α} (hx : J.Inc e₁ x) (hy : J.Inc e₂ y) (h₁ : P e₁) (h₂ : ¬ P e₂) :
    ∃ w e e', J.Inc e w ∧ J.Inc e' w ∧ P e ∧ ¬ P e' := by
  by_contra hno
  push Not at hno
  have hwalk : ∀ {z t : α} (p : J.skeleton.Walk z t), (∃ e, J.Inc e z ∧ P e) →
      ∃ e, J.Inc e t ∧ P e := by
    intro z t p
    induction p with
    | nil => exact id
    | cons hadj _ ih =>
      rintro ⟨e, hez, hPe⟩
      obtain ⟨-, f, hfz, hfz'⟩ := hadj
      exact ih ⟨f, hfz', hno _ e f hez hfz hPe⟩
  obtain ⟨p⟩ := hconn x (J.vertex_mem_of_inc hx) y (J.vertex_mem_of_inc hy)
  obtain ⟨e, hey, hPe⟩ := hwalk p ⟨e₁, hx, h₁⟩
  exact h₂ (hno y e e₂ hey hy hPe)

/-- A vertex that is an end of two different edges of `J` is not a terminal of `J`. -/
theorem not_mem_terminals_of_inc {J : Hypergraph α β} {w : α} {e e' : β} (he : J.Inc e w)
    (he' : J.Inc e' w) (hne : e ≠ e') : w ∉ terminals J := by
  rintro ⟨-, hdeg⟩
  have hfin : (incidentEdges J w).Finite := J.edgeSet_finite.subset fun _ h => h.1
  have h2 : 1 < (incidentEdges J w).ncard :=
    (one_lt_ncard_iff hfin).mpr ⟨e, e', ⟨J.edge_mem_of_inc he, he⟩, ⟨J.edge_mem_of_inc he', he'⟩,
      hne⟩
  have : (incidentEdges J w).ncard ≤ vertexDegree J w := Nat.le_add_right _ _
  omega

variable {S : Type w} [TopologicalSpace S] [T2Space S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
  {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {S₁ S₂ F : Set S} {a b : S}
  (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (h : IsSideOfLine Γ S₁ S₂ F a b)
include hP h

/-- **A jump on one side.** A `Σ`-jump whose edges all lie in `S₁` is an `S₁`-jump of
`Γ ∩ S₁`. Its vertices lie in `S₁`, since each is an end of one of its edges. Its ends are in
`bd(S₁)`, and a vertex of `Γ ∩ S₁` in `bd(S₁)` lies in `bd(S)`, because the only vertices of `Γ`
on `F` are `a, b ∈ bd(S)`. -/
theorem isSigmaJump_side {J : Hypergraph α β} (hJ : IsSigmaJump Γ Γ_sub ιV J)
    (hall : ∀ e ∈ J.edgeSet, ∃ e' ∈ Γ.E, e' ⊆ S₁ ∧ ιE e' = e) :
    IsSigmaJump (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁)
      (ιV ∘ Subtype.val) J := by
  have hS := hP.is_surface
  obtain ⟨hJΓ, hpath, u, hu, v, hv, huv, hterm, hint⟩ := hJ
  have hιuv : ιV u ≠ ιV v := fun he => huv (hP.ιV_injOn hu.1 hv.1 he)
  have huJ : ιV u ∈ J.vertexSet := (hterm.symm ▸ Or.inl rfl : ιV u ∈ terminals J).1
  have hvJ : ιV v ∈ J.vertexSet := (hterm.symm ▸ Or.inr rfl : ιV v ∈ terminals J).1
  -- Every vertex of `J` is `ιV` of a vertex of `Γ` in `S₁`.
  have hVJ : J.vertexSet ⊆ ιV '' (Γ.V ∩ S₁) := by
    intro x hx
    obtain ⟨y, hyJ, hxy⟩ : ∃ y ∈ J.vertexSet, x ≠ y := by
      by_cases hxu : x = ιV u
      · exact ⟨ιV v, hvJ, hxu ▸ hιuv⟩
      · exact ⟨ιV u, huJ, hxu⟩
    obtain ⟨p⟩ := hpath.2.2.1 x hx y hyJ
    obtain ⟨e, hex⟩ : ∃ e, J.Inc e x := by
      cases p with
      | nil => exact (hxy rfl).elim
      | cons hadj _ => obtain ⟨-, e, hex, -⟩ := hadj; exact ⟨e, hex⟩
    obtain ⟨e', he', he'S₁, rfl⟩ := hall e (J.edge_mem_of_inc hex)
    have hexΓ : Γ_sub.Inc (ιE e') x := GM10.inc_of_le hJΓ hex
    have hxΓ : x ∈ Γ_sub.vertexSet := Γ_sub.vertex_mem_of_inc hexΓ
    rw [← hP.ιV_image] at hxΓ
    obtain ⟨x', hx'V, rfl⟩ := hxΓ
    exact ⟨x', ⟨hx'V, closure_minimal he'S₁ h.isClosed_left
      ((hP.inc_iff e' he' x' hx'V).mp hexΓ)⟩, rfl⟩
  have hmemS₁ : ∀ {x : S}, x ∈ Γ.V → ιV x ∈ J.vertexSet → x ∈ S₁ := by
    intro x hxV hx
    obtain ⟨x', hx', hxx'⟩ := hVJ hx
    rw [← hP.ιV_injOn hx'.1 hxV hxx']
    exact hx'.2
  have hle : J ≤ sideSub Γ Γ_sub ιV ιE S₁ := by
    refine le_subOn hJΓ hVJ ?_
    intro e he
    obtain ⟨e', he', he'S₁, rfl⟩ := hall e he
    exact ⟨e', ⟨he', he'S₁⟩, rfl⟩
  have hbd : ∀ {x : S₁}, x.1 ∈ Γ.V → (x ∈ bd S₁ ↔ x.1 ∈ bd S) := by
    intro x hxV
    rw [h.mem_bd_iff hS]
    exact ⟨fun hx => hx.elim (fun hxF => h.mem_bd_of_mem_V hxF hxV) id, Or.inr⟩
  have huS₁ := hmemS₁ hu.1 huJ
  have hvS₁ := hmemS₁ hv.1 hvJ
  refine ⟨hle, hpath, ⟨u, huS₁⟩, ⟨?_, (hbd hu.1).mpr hu.2⟩, ⟨v, hvS₁⟩, ⟨?_, (hbd hv.1).mpr hv.2⟩,
    fun he => huv (congrArg Subtype.val he), hterm, ?_⟩
  · rw [sideDrawing_V]; exact hu.1
  · rw [sideDrawing_V]; exact hv.1
  · rintro x ⟨hxV, hxbd⟩ hxJ
    rw [sideDrawing_V] at hxV
    rcases hint x.1 ⟨hxV, (hbd hxV).mp hxbd⟩ hxJ with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)

/-- **Every `Σ`-jump lies on one side** (Graph Minors XXI, proofs of (6.6), (6.7) and of claim (4)
of (6.3)). A `Σ`-jump of `Γ` is a `Σ₁`-jump of `Γ ∩ Σ₁` or a `Σ₂`-jump of `Γ ∩ Σ₂`. -/
theorem sigmaJumps_subset_side :
    sigmaJumps Γ Γ_sub ιV ⊆
      sigmaJumps (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁) (ιV ∘ Subtype.val) ∪
      sigmaJumps (sideDrawing Γ h.symm.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₂)
        (ιV ∘ Subtype.val) := by
  intro J hJ
  have hJ' := hJ
  obtain ⟨hJΓ, hpath, u, hu, v, hv, huv, hterm, hint⟩ := hJ'
  -- Each edge of `J` is `ιE e'` for an edge `e'` of `Γ`.
  have hedge : ∀ e ∈ J.edgeSet, ∃ e' ∈ Γ.E, ιE e' = e := by
    intro e he
    have heΓ := hJΓ.edgeSet_subset he
    rw [← hP.ιE_image] at heΓ
    exact heΓ
  have hend : ∀ e ∈ J.edgeSet, ∃ x, J.Inc e x := by
    intro e he
    have h2 := hpath.2.2.2.1 e he
    obtain ⟨x, hx⟩ := nonempty_of_ncard_ne_zero (s := J.ends e) (by omega)
    exact ⟨x, hx⟩
  let P : β → Prop := fun e => ∃ e' ∈ Γ.E, e' ⊆ S₁ ∧ ιE e' = e
  by_cases hall : ∀ e ∈ J.edgeSet, P e
  · exact Or.inl (isSigmaJump_side hP h hJ hall)
  by_cases hnone : ∀ e ∈ J.edgeSet, ¬ P e
  · refine Or.inr (isSigmaJump_side hP h.symm hJ fun e he => ?_)
    obtain ⟨e', he', rfl⟩ := hedge e he
    refine ⟨e', he', ?_, rfl⟩
    exact subset_two_of_disjoint h.union_eq ((h.edge_subset_or_disjoint he').resolve_left
      fun hS₁ => hnone _ he ⟨e', he', hS₁, rfl⟩)
  -- Otherwise two edges of `J` lie on different sides.
  push Not at hall hnone
  obtain ⟨e₂, he₂, hPe₂⟩ := hall
  obtain ⟨e₁, he₁, hPe₁⟩ := hnone
  obtain ⟨x, hx⟩ := hend e₁ he₁
  obtain ⟨y, hy⟩ := hend e₂ he₂
  obtain ⟨w, e, e', hew, he'w, hPe, hPe'⟩ := exists_inc_of_reachable P hpath.2.2.1 hx hy hPe₁ hPe₂
  have hne : e ≠ e' := fun he => hPe' (he ▸ hPe)
  have hwT := not_mem_terminals_of_inc hew he'w hne
  obtain ⟨f, hf, hfS₁, rfl⟩ := hPe
  obtain ⟨f', hf', rfl⟩ := hedge e' (J.edge_mem_of_inc he'w)
  have hf'S₂ : closure f' ⊆ S₂ := h.closure_subset_right_of_disjoint
    ((h.edge_subset_or_disjoint hf').resolve_left fun hS₁ => hPe' ⟨f', hf', hS₁, rfl⟩)
  have hwΓ : Γ_sub.Inc (ιE f) w := GM10.inc_of_le hJΓ hew
  have hwΓ' : Γ_sub.Inc (ιE f') w := GM10.inc_of_le hJΓ he'w
  have hwV : w ∈ Γ_sub.vertexSet := Γ_sub.vertex_mem_of_inc hwΓ
  rw [← hP.ιV_image] at hwV
  obtain ⟨w', hw'V, rfl⟩ := hwV
  have hw'S₁ : w' ∈ S₁ := closure_minimal hfS₁ h.isClosed_left ((hP.inc_iff f hf w' hw'V).mp hwΓ)
  have hw'S₂ : w' ∈ S₂ := hf'S₂ ((hP.inc_iff f' hf' w' hw'V).mp hwΓ')
  have hw'F : w' ∈ F := h.inter_eq ▸ ⟨hw'S₁, hw'S₂⟩
  rcases hint w' ⟨hw'V, h.mem_bd_of_mem_V hw'F hw'V⟩ (J.vertex_mem_of_inc hew) with rfl | rfl
  · exact (hwT (hterm ▸ Or.inl rfl)).elim
  · exact (hwT (hterm ▸ Or.inr rfl)).elim

/-- The number of `Σ`-jumps of `Γ` is at most the number of `Σ₁`-jumps of `Γ ∩ Σ₁` plus the number
of `Σ₂`-jumps of `Γ ∩ Σ₂`. -/
theorem encard_sigmaJumps_le_side :
    (sigmaJumps Γ Γ_sub ιV).encard ≤
      (sigmaJumps (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁)
        (ιV ∘ Subtype.val)).encard +
      (sigmaJumps (sideDrawing Γ h.symm.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₂)
        (ιV ∘ Subtype.val)).encard :=
  (encard_le_encard (sigmaJumps_subset_side hP h)).trans (encard_union_le _ _)

end Side
end GM21
end GraphMinor
