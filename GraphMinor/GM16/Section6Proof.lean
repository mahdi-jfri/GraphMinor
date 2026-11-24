module

public import GraphMinor.GM16.Section6
public import GraphMinor.GM12.Bridge
import GraphMinor.GM16.Section6ClusterProof
import GraphMinor.GM16.Section6ClearedHairGraph
import GraphMinor.GM16.Section6Clearing
import GraphMinor.GM16.Section6Animals
import GraphMinor.GM16.Section6CliqueLinkage
import GraphMinor.GM16.Section8Truncation
import GraphMinor.GM16.Section5Proof
import GraphMinor.GM16.Section5Degree
import GraphMinor.GM16.Section5Connections
import GraphMinor.GM16.Section6Linkages
import GraphMinor.GM16.Section6ZoneWalks
import GraphMinor.GM09.Basic
import GraphMinor.GM14.Section3b
import GraphMinor.GM11.Section810


import GraphMinor.GM11.CitedResults

import GraphMinor.GM12.Bridge

import GraphMinor.GM12.Section710

import GraphMinor.GM14.Section9a

import GraphMinor.GM14.Section9b

/-!
# Graph Minors XVI (6.3)

Bound the active hairs by (5.3), select a large cluster of far hair ends,
and clear a zone containing them. The remaining drawing is a span and
retains the near hair ends, which stay far apart in its metric. Join the
far ends inside the smaller zone. A second application of (5.3) to this
connected graph gives either the clique minor or an extra horn.

On page 60, the connected subgraph must contain the far ends `v(y)`,
rather than `Y₄` as printed. Claim (3) puts `Y₄` outside the cleared zone.
The construction here uses the corrected far ends. See the correction to the
proof of (6.3) in `corrections/GM16.md`.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Explicit hair count `δ` for Graph Minors XVI, (6.3). -/
@[expose] def theorem_6_3_delta (p τ : ℕ) : ℕ :=
  2 * (p * (p - 1) / 2) ^ 2 * (max τ 2) ^ 2

/-- Explicit threshold `θ` for Graph Minors XVI, (6.3). -/
@[expose] def theorem_6_3_theta (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p ψ : ℕ) : ℕ :=
  5 * max ψ (max 3 (GM12.theorem_4_4_bound V a b p)) + 34

/-- **Graph Minors XVI, (6.3)** (pages 59–61), with explicit parameters
`theorem_6_3_delta p τ` and `theorem_6_3_theta V a b p ψ`. -/
theorem theorem_6_3_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (p τ χ ψ : ℕ) (hψ : 1 ≤ ψ) :
    1 ≤ theorem_6_3_theta V a b p ψ ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β)),
      IsGraphTangle G θ_star T_star →
      HasAnimal S G T_star θ_star χ (theorem_6_3_delta p τ)
        (theorem_6_3_theta V a b p ψ) (τ + 1) →
      HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ ∨
      ControlsMinor G (completeGraph p) T_star := by
  classical
  let : ConnectedSpace S := hConn
  let μ := p * (p - 1) / 2
  let τ' := max τ 2
  let r₀ := GM12.theorem_4_4_bound V a b p
  have hr₀_spec : IsMarkedPathThreshold.{u, v, w} S p r₀ :=
    clique_threshold_for_marked_paths_explicit.{u, v, w} V hV hS hConn he p
  let r := max ψ (max 3 r₀)
  let θ := theorem_6_3_theta V a b p ψ
  let δ := theorem_6_3_delta p τ
  have hψr : ψ ≤ r := le_max_left _ _
  have h3r : 3 ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hr₀ : r₀ ≤ r := (le_max_right _ _).trans (le_max_right _ _)
  have hττ' : τ ≤ τ' := le_max_left _ _
  have hτ' : 2 ≤ τ' := le_max_right _ _
  have hrθ : r ≤ θ := by dsimp only [θ, theorem_6_3_theta, r, r₀]; omega
  refine ⟨by dsimp only [θ, theorem_6_3_theta]; omega, ?_⟩
  intro α β G θ_star T_star hT hAnimal
  by_cases hClique : ControlsMinor G (completeGraph p) T_star
  · exact Or.inr hClique
  by_cases hNew : HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ
  · exact Or.inl hNew
  apply False.elim
  obtain ⟨H, η, θ_span, T₀, d₀, X, Y, hAnim₀⟩ := hAnimal
  let T := GM10.truncation T₀ θ
  let d : Set S → Set S → ℕ := fun a b => min (d₀ a b) θ
  have hAnim : IsAnimal G T_star θ_star H η θ T d X Y χ δ θ (τ + 1) :=
    theorem_8_3_claim_1 hAnim₀
  have hSaved := hAnim
  obtain ⟨_, _, hSpan, hMet, hXsub, hXcard, hYsub, _, hHorns, _, hSep⟩ := hAnim
  by_cases hμzero : μ = 0
  · exact hClique (controlsMinor_of_zero_pairs_of hr₀_spec hSpan hMet (hr₀.trans hrθ) hμzero)
  have hμ : 1 ≤ μ := by omega
  obtain ⟨F⟩ := hSaved.exists_hairFamily
  obtain ⟨_, hself, _, hsymm, htri, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ T d hS hConn hMet
  have hselfV : ∀ a ∈ H.V, d {a} {a} = 0 := fun a ha =>
    hself {a} (singleton_mem_A_of_mem_V ha)
  have hsymV : ∀ a ∈ H.V, ∀ b ∈ H.V, d {a} {b} = d {b} {a} := fun a ha b hb =>
    hsymm {a} (singleton_mem_A_of_mem_V ha) {b} (singleton_mem_A_of_mem_V hb)
  have htriV : ∀ a ∈ H.V, ∀ b ∈ H.V, ∀ c ∈ H.V,
      d {a} {c} ≤ d {a} {b} + d {b} {c} := fun a ha b hb c hc =>
    htri {a} (singleton_mem_A_of_mem_V ha) {b} (singleton_mem_A_of_mem_V hb)
      {c} (singleton_mem_A_of_mem_V hc)
  obtain ⟨w, hw, Y₄, hY₄, hY₄card, hnearFar⟩ := theorem_6_3_far_end_cluster_of hr₀_spec
    hSaved F hμ rfl hr₀ (by omega) (by dsimp only [θ, theorem_6_3_theta, r, r₀]; omega)
    hψ (hψr.trans hrθ) (Nat.le_succ τ) hττ' hτ' hselfV hsymV htriV hClique hNew
  have hwA := singleton_mem_A_of_mem_V hw
  obtain ⟨Λ₁, hZone₁, hcontain₁⟩ := GraphMinor.GM14.theorem_9_2_proof.{w} H θ r T d {w} hS hConn hMet hwA
    (by omega) (by dsimp only [θ, theorem_6_3_theta, r, r₀]; omega)
  obtain ⟨Λ, hZone, hRigid, hcontain⟩ := GraphMinor.GM14.theorem_9_3_proof.{w} H θ (r + 3) T d {w} hS hConn hSpan.isRigid hMet hwA
    (by omega) (by dsimp only [θ, theorem_6_3_theta, r, r₀]; omega)
  change IsLambdaZoneAround H d (r + 8) {w} Λ at hZone
  have hnest : closure Λ₁ ⊆ Λ := zone_closure_subset_of_atom_neighborhood hZone₁
    (by intro a ha hd; exact hcontain a ha hd)
  have hfarΛ₁ : ∀ y ∈ Y₄, F.far y ∈ closure Λ₁ := by
    intro y hy
    have hfarH := F.far_mem y (hY₄ hy)
    have hd : d {w} {F.far y} < r := by
      rw [hsymV w hw (F.far y) hfarH]
      exact hnearFar y hy
    exact subset_closure (hcontain₁ {F.far y} (singleton_mem_A_of_mem_V hfarH) hd (mem_singleton _))
  have hnearOut : ∀ y ∈ Y₄, y ∉ Λ := by
    intro y hy hyΛ
    have hyH := hYsub (hY₄ hy)
    have hfarH := F.far_mem y (hY₄ hy)
    have hbound := hZone.dist_le {y} (singleton_mem_A_of_mem_V hyH)
      (singleton_subset_iff.mpr (subset_closure hyΛ))
    have htri' := htriV y hyH w hw (F.far y) hfarH
    rw [hsymV y hyH w hw, hsymV w hw (F.far y) hfarH] at htri'
    have hfar := F.dist y (hY₄ hy)
    have hnear := hnearFar y hy
    change 5 * r + 34 ≤ d {y} {F.far y} at hfar
    omega
  let H' := clearedSubdrawing H Λ
  let η' := restrictCleared η Λ
  obtain ⟨T', d', hClear, _⟩ := GraphMinor.GM14.theorem_3_2_proof hS hConn
    (by dsimp only [θ, theorem_6_3_theta, r, r₀]; omega : 4 * (r + 8) + 3 ≤ θ) hMet hZone
  have horder : θ - 4 * (r + 8) - 2 = r := by dsimp only [θ, theorem_6_3_theta, r, r₀]; omega
  have hSpan' : IsSigmaSpan G H' η' θ_star r T_star T' := by
    simpa only [horder] using IsSigmaSpan.clear hSpan hClear hRigid
  have hMet' : HasTangleMetric H' r T' d' := by
    simpa only [horder] using hClear.hasMetric
  have hY₄new : ∀ y ∈ Y₄, y ∈ H'.V := fun y hy =>
    mem_clearedSubdrawing_V (hYsub (hY₄ hy)) (hnearOut y hy)
  have hSep' : ∀ y ∈ Y₄, ∀ z ∈ Y₄, y ≠ z → r ≤ d' {y} {z} := by
    intro y hy z hz hyz
    have hdist := hSep y (hY₄ hy) z (hY₄ hz) hyz
    have hbound := (hClear.dist_bounds {y} (singleton_mem_A_of_mem_V (hYsub (hY₄ hy)))
      {z} (singleton_mem_A_of_mem_V (hYsub (hY₄ hz)))
      {y} (singleton_mem_A_of_mem_V (hY₄new y hy))
      {z} (singleton_mem_A_of_mem_V (hY₄new z hz)) Subset.rfl Subset.rfl).1
    change 5 * r + 34 ≤ d {y} {z} at hdist
    omega
  have hXnew : X ⊆ V(G) \ V(η'.imageGraph) := by
    intro x hx
    exact ⟨(hXsub hx).1, fun hx' => (hXsub hx).2
      ((restrictCleared_imageGraph_le η Λ).vertexSet_mono hx')⟩
  have hOldHorns : ∀ x ∈ X, ∃ (P : Fin τ → Graph α β) (ends : Fin τ → S),
      IsHorn G H' η' d' x r τ P ends := by
    intro x hx
    obtain ⟨P, ends, hHorn⟩ := hHorns x hx
    have h62 := theorem_6_2_proof hS hConn G θ_star θ (r + 8) τ T_star H η T T' d d' Λ x P ends
      hSpan hMet (by omega) (by dsimp only [θ, theorem_6_3_theta, r, r₀]; omega)
      ⟨{w}, hwA, hZone⟩ hRigid hClear hHorn
    simpa only [horder] using h62
  have hBase : IsAnimal G T_star θ_star H' η' r T' d' X ∅ χ 0 r τ :=
    ⟨by omega, le_rfl, hSpan', hMet', hXnew, hXcard, empty_subset _, ncard_empty S,
      hOldHorns, fun _ h => False.elim h, fun _ h => False.elim h⟩
  obtain ⟨K, hKG, hConnK, hXK, hKH, hInter, hLeaf⟩ := exists_connected_cleared_hair_graph
    hS F hYsub hXsub hMet.1.1 hZone₁ hZone.isOpenDisc.1 hnest hY₄ hfarΛ₁ hnearOut
  let A := η'.vMap '' Y₄
  have hAK : A ⊆ V(K) := by
    intro x hx
    have hx' : x ∈ V(K) ∩ V(η'.imageGraph) := hInter.symm ▸ hx
    exact hx'.1
  have hAH : A ⊆ V(η'.imageGraph) := by
    rintro x ⟨y, hy, rfl⟩
    exact η'.bijOn_v.mapsTo (hY₄new y hy)
  have hAcard : A.ncard = Y₄.ncard := (η'.bijOn_v.injOn.mono hY₄new).ncard_image
  have hμτ : 2 ≤ μ * τ' := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hμ hτ'
  change μ * τ' ≤ Y₄.ncard at hY₄card
  have hA2 : 1 < A.ncard := by omega
  have hcompA : ∀ a ∈ A, ∃ b ∈ A, b ≠ a ∧ Relation.ReflTransGen K.Adj a b := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := exists_ne_of_one_lt_ncard hA2 a
    obtain ⟨W⟩ := hConnK.2 a (hAK ha) b (hAK hb)
    exact ⟨b, hb, hba, graphWalk_adj_reachable W⟩
  have hcountA : τ' * (μ - 1) < A.ncard := by
    have hpred : μ - 1 + 1 = μ := by omega
    have hsum : τ' * (μ - 1) + τ' = μ * τ' := by
      calc
        τ' * (μ - 1) + τ' = (μ - 1 + 1) * τ' := by ring
        _ = μ * τ' := by rw [hpred]
    have hstrict : τ' * (μ - 1) < μ * τ' := by omega
    omega
  have hKV := hT.finite_V.subset hKG.vertexSet_mono
  have hKE := hT.finite_E.subset hKG.edgeSet_mono
  rcases theorem_5_3_proof K A μ τ' hKV hKE hAK hcompA hcountA with
    ⟨P, a, b, hPP, hP⟩ | ⟨x, P, b, hxK, hinter, hP⟩
  · apply hClique
    apply hr₀_spec G K θ_star r T_star H' η' T' d' Y₄
      P a b hSpan' hMet' hr₀ hY₄new
      (fun y hy z hz hyz => hr₀.trans (hSep' y hy z hz hyz)) hKG hKH hInter.subset
    · intro i
      obtain ⟨ha, hb, hab, hp, _⟩ := hP i
      exact ⟨hAH ha, hAH hb, hab, hp⟩
    · exact hPP
  · have hxH : x ∉ V(η'.imageGraph) := by
      intro hxH
      have hl := hLeaf x hxH
      have hc : {z | K.Adj x z}.ncard ≤ 1 :=
        (ncard_le_one hl.finite).mpr (fun _ ha _ hb => hl ha hb)
      have hf := fan_card_le_neighbors_ncard hKV
        (fun i => ⟨(hP i).2.1, (hP i).2.2.1⟩)
        (fun i j hij => (hinter i j hij).1.subset)
      omega
    obtain ⟨R, ends, hHorn⟩ := horn_of_fan_in_subgraph hKG hxK hxH hInter.subset hY₄new
      (fun y hy z hz hyz => hψr.trans (hSep' y hy z hz hyz))
      (fun i => ⟨hAH (hP i).1, (hP i).2.2.1⟩) hinter
    have hxX : x ∉ X := fun hxX => (Set.disjoint_left.mp hXK) hxX hxK
    exact hNew (hBase.add_horn hψ hψr le_rfl hxX ⟨_, _, hHorn.mono le_rfl hττ'⟩)

/-- **Graph Minors XVI, (6.3)** (pages 59–61), by the two applications
of (5.3), the maximal separated hair family, and clearing the far-end
cluster. The page-60 typo concerning the vertices of `H₂` is corrected
by joining the far ends inside the smaller closed zone. -/
theorem theorem_6_3_proof
     : GM16Theorem63Statement.{u, v, w} := by
  intro S _ _ hS hConn p τ χ ψ hψ
  let : ConnectedSpace S := hConn
  obtain ⟨a, b, he⟩ := GM12.exists_closed_surface_model hS
  exact ⟨theorem_6_3_delta p τ, theorem_6_3_theta GM07.vModel a b p ψ,
    theorem_6_3_explicit.{u, v, w} GM07.vModel (fun _ _ _ _ => le_rfl) hS hConn he p τ χ ψ hψ⟩

end GraphMinor.GM16
