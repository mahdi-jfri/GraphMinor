module

public import GraphMinor.GM21.Section6CutJumps
public import GraphMinor.GM21.Section6CutLinkage
public import GraphMinor.GM21.Section6Induction
import GraphMinor.GM21.Section6CutCuffs
import GraphMinor.GM21.Section6Exhaustive
import GraphMinor.GM21.LinkageLemmas

/-!
# Graph Minors XXI, (6.3), claim (2)

"(2) *We may assume that every proper line $F \subseteq \Sigma$ with ends in $V(\Gamma)$ and with
no internal point in $U(\Gamma)$ separates $\Sigma$.*" (page 28 of the preprint.)

`claim_2`: if cutting `Σ` along such a line `F` gives a connected surface `Σ'` of smaller type,
then `Γ` has at most `λ(p + 4q, q, r + 2)` jumps. The proof is the paper's:
* the drawing `Γ'` on `Σ'` (`exists_cutDrawing`);
* the pieces of the supports at the ends `a, b` of `F` (`isPieceSystem_D` when `a, b` lie in
  different supports, the case of the paper; `isPieceSystem_S` when they lie in one support);
* the presentation of the split graph `G'` in `Σ'` of defect `r + 2` (`isPresentation_of_system`);
* the exhaustive vital `(p + 4q)`-linkage of `G'` from (2.4) (`isExhaustiveLinkage_cut`);
* the jumps of `Γ` give distinct jumps of `Γ'` (`encard_sigmaJumps_le_cut`), and these are at most
  `λ(p + 4q, q, r + 2)` by the inductive hypothesis (1).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM21.Split
open GraphMinor.GM21.Induction

universe u v

variable {α : Type u} {β : Type v} {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r' : ℕ} {F_star : Fin r' → Set S} {H : Fin r' → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {qf : Fin r' → ℕ} {L : Hypergraph α β}

/-- Every edge of `Γ` has two different ends, since `Γ` is part of a linkage. -/
theorem two_ends_of_linkage (hP : IsPresentation G Γ Γ_sub ιV ιE r' F_star H μ qf)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) :
    ∀ e ∈ Γ.E, ∃ u w, u ≠ w ∧ closure e ∩ Γ.V = {u, w} := by
  have hK := IsExhaustiveLinkage.isLinkage hP hL
  intro e he
  have heΓ : ιE e ∈ Γ_sub.edgeSet := hP.ιE_image ▸ mem_image_of_mem ιE he
  have h2 := hK.ends_ncard_eq_two heΓ
  have hends : Γ_sub.ends (ιE e) = ιV '' (closure e ∩ Γ.V) := by
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq]
    constructor
    · intro hx
      have hxV : x ∈ ιV '' Γ.V := hP.ιV_image ▸ Γ_sub.vertex_mem_of_inc hx
      obtain ⟨u, hu, rfl⟩ := hxV
      exact ⟨u, ⟨(hP.inc_iff e he u hu).mp hx, hu⟩, rfl⟩
    · rintro ⟨u, ⟨hue, hu⟩, rfl⟩
      exact (hP.inc_iff e he u hu).mpr hue
  rw [hends, (hP.ιV_injOn.mono inter_subset_right).ncard_image] at h2
  obtain ⟨u, w, huw, hs⟩ := ncard_eq_two.mp h2
  exact ⟨u, w, huw, hs⟩

/-- **The bound from a system of pieces.** If the cut surface `Σ'` has smaller type, then a system
of `r₂ ≤ r + 2` pieces gives at most `λ(p + 4q, q, r + 2)` jumps. -/
theorem jumps_le_of_system {n c : ℕ} [ConnectedSpace S'] {n' c' : ℕ} (hT' : HasType S' n' c')
    (hlt : TypeLt n' c' n c) {p qq r lam : ℕ}
    (hlam : BoundBelow.{u, v} n c (p + 4 * qq) qq (r + 2) lam) (hG : G.IsGraph)
    (hP : IsPresentation G Γ Γ_sub ιV ιE r' F_star H μ qf) (hqf : ∀ j, qf j ≤ qq)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) (hFU : F ∩ Γ.U ⊆ {a, b}) {cb : Bool} {Apf Bpf : Set S}
    (hApf : ∃ j, Apf ⊆ F_star j) (hBpf : ∃ j, Bpf ⊆ F_star j) {r₂ : ℕ} (hr₂ : r₂ ≤ r + 2)
    (hr₂0 : r₂ ≠ 0) {P : Fin r₂ → Set S} {τ : Fin r₂ → Fin r'} {col : Fin r₂ → Bool × Bool}
    (hsys : IsPieceSystem G Γ Γ_sub μ F_star a b cb Apf Bpf P τ col) :
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam := by
  have hS := hP.is_surface
  have ha : a ∈ Γ.V ∩ bd S := ⟨habV.1, hF.2.1⟩
  have hb : b ∈ Γ.V ∩ bd S := ⟨habV.2, hF.2.2.1⟩
  have hFU' : F ∩ Γ.U ⊆ Γ.V := fun x hx => by
    rcases hFU hx with rfl | rfl
    exacts [habV.1, habV.2]
  obtain ⟨Γ', hU, hV, hΓ', hE⟩ := h.exists_cutDrawing hS hF hP.is_proper_drawing hFU'
  have hcuff := h.two_le_ncard_cuff hS hF habV hP.cuff_vertices_ge_two hV
  have hlink := two_ends_of_linkage hP hL
  obtain ⟨am, ap, bm, bp, hpa, hamp, hpb, hbmp, hA, hB⟩ := exists_sides_of_system hP h hF hsys
  have hPres := isPresentation_of_system hP h hF habV hFU hU hV hE hΓ' hcuff hpa hamp hpb hbmp
    hlink hApf hBpf hsys hA hB
  obtain ⟨hExh, hLp₂⟩ := isExhaustiveLinkage_cut hP ha hb hF.ne hsys
    (cutEdges G Γ μ ψ ιE Apf ap) (cutEdges G Γ μ ψ ιE Bpf bp) hPres.drawing_subgraph
    (fun e he => hP.ιE_image ▸ he.1) hqf hL hLp
  refine (encard_sigmaJumps_le_cut hP h hF habV hFU hV hpa hamp hpb hbmp cb
    (cutEdges G Γ μ ψ ιE Apf ap) (cutEdges G Γ μ ψ ιE Bpf bp)).trans ?_
  exact hlam S' h.surface n' c' hT' hlt _ Γ' _ _ _ r₂ _ _ _ _ (isGraph_split2 hG) hr₂
    ⟨_, hPres, fun i => hqf _, fun h0 => absurd h0 hr₂0⟩ hExh hLp₂

/-- **Claim (2) of the proof of (6.3)** (Graph Minors XXI, page 28 of the preprint). Let `F` be a
proper line in `Σ` with ends `a, b ∈ V(Γ)` and no internal point in `U(Γ)`, and let the surface `Σ'`
cut from `Σ` along `F` be connected and of smaller type. Then `Γ` has at most `λ(p + 4q, q, r + 2)`
jumps. -/
theorem claim_2 {n c : ℕ} [ConnectedSpace S'] {n' c' : ℕ} (hT' : HasType S' n' c')
    (hlt : TypeLt n' c' n c) {p q r lam : ℕ}
    (hlam : BoundBelow.{u, v} n c (p + 4 * q) q (r + 2) lam) (hG : G.IsGraph) (hr : r' ≤ r)
    (hd : PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) (hFU : F ∩ Γ.U ⊆ {a, b}) :
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam := by
  obtain ⟨qf, hP, hqf, -⟩ := hd
  have ha : a ∈ Γ.V ∩ bd S := ⟨habV.1, hF.2.1⟩
  have hb : b ∈ Γ.V ∩ bd S := ⟨habV.2, hF.2.2.1⟩
  obtain ⟨ja, hja⟩ := mem_iUnion.mp (hP.bd_vertices_covered ha)
  obtain ⟨jb, hjb⟩ := mem_iUnion.mp (hP.bd_vertices_covered hb)
  let e : Fin (r' + 2) ≃ Option (Option (Fin r')) :=
    (finSuccEquiv (r' + 1)).trans (Equiv.optionCongr (finSuccEquiv r'))
  by_cases hj : ja = jb
  · subst hj
    obtain ⟨Am, Ap, Bm, Bp, M, hHa, hMa, hHb, hMb, hM, h1, h2, h3, h4, h5⟩ :=
      exists_halves_pair hP ja ⟨habV.1, hja⟩ ⟨habV.2, hjb⟩ hF.ne
    exact jumps_le_of_system hT' hlt hlam hG hP hqf hL hLp h hF habV hFU ⟨ja, hHa.right_subset⟩
      ⟨ja, hHb.right_subset⟩ (by omega) (by omega)
      ((isPieceSystem_S hP hG ⟨habV.1, hja⟩ ⟨habV.2, hjb⟩ hF.ne hHa hMa hHb hMb hM h1 h2 h3 h4
        h5).comp_equiv e)
  · obtain ⟨Am, Ap, hHa, hMa⟩ := exists_halves hP ja ⟨habV.1, hja⟩
    obtain ⟨Bm, Bp, hHb, hMb⟩ := exists_halves hP jb ⟨habV.2, hjb⟩
    exact jumps_le_of_system hT' hlt hlam hG hP hqf hL hLp h hF habV hFU ⟨ja, hHa.right_subset⟩
      ⟨jb, hHb.right_subset⟩ (by omega) (by omega)
      ((isPieceSystem_D hP hG ⟨habV.1, hja⟩ ⟨habV.2, hjb⟩ hj hHa hMa hHb hMb).comp_equiv e)

end CutLine
end GM21
end GraphMinor
