module

public import GraphMinor.GM12.Cited
public import GraphMinor.GM12.Defs
public import GraphMinor.GM15.Defs
public import GraphMinor.GM16.Defs
public import GraphMinor.GM12.Section4EyeConnections
import GraphMinor.GM12.Section4EyeBranchControl
import GraphMinor.GM12.Section4EyePathReindex
import GraphMinor.GM12.Section4Monotone
import GraphMinor.GM12.Section2NonemptyEdges

import GraphMinor.GM07.Section7
import GraphMinor.GM07.Bridge

/-!
# Graph Minors XII (4.5): the construction for large cliques

Use the source subdivision, ordered eye discs, and endpoint
connections of page 253. Renumber the two external paths at
each eye by the source edges. The connected classes and those
paths give a controlled source minor by the two-region branch
estimate. Apply (4.2) to its complete-graph minor.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph Hypergraph GM14 GM15

universe u

/-- XII (4.5), pages 252--253, for `p ≥ 4`, with explicit eye count
`theorem_4_5_large_kBound p` and explicit threshold `theorem_4_5_large_NBound V a b p`. -/
theorem theorem_4_5_span_large_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a₀ b₀ : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a₀ b₀ 0))
    (p : ℕ) (hp : 4 ≤ p) :
    ∀ {α β : Type*} (G : Graph α β) (θstar θ : ℕ)
      (Tstar : Set (Hypergraph α β × Hypergraph α β)) (Γ : Drawing S)
      (η : SpanEmbedding Γ G) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → theorem_4_5_large_NBound V a₀ b₀ p ≤ θ →
      ∀ (r : Fin (theorem_4_5_large_kBound p) → Set S)
        (P Q : Fin (theorem_4_5_large_kBound p) → Graph α β),
      Function.Injective r → (∀ i, IsEyeWithPaths G Γ η θ T (r i) (P i) (Q i)) →
      (∀ i j, i ≠ j → theorem_4_5_large_NBound V a₀ b₀ p ≤ d (r i) (r j)) →
      (∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
        ((P j).vertexSet ∪ (Q j).vertexSet)) →
      ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  classical
  obtain ⟨W, E, L, κ, t, σ, hW, hE, hminor, hlink, hκne, ht, htle, hNW, htwo, hconnect⟩ :=
    exists_eye_connections_explicit V hV hS he hp
  let : Finite W := hW
  let : Finite E := hE
  let : Fintype W := Fintype.ofFinite W
  let : Fintype E := Fintype.ofFinite E
  set N := theorem_4_5_large_NBound V a₀ b₀ p
  intro α β G θstar θ Tstar Γ η T d hCtrl hm hN r₀ P₀ Q₀ hri₀ heye₀ hfar₀ hdisj₀
  let emb : Fin t → Fin (theorem_4_5_large_kBound p) := Fin.castLE htle
  have hemb : Function.Injective emb := Fin.castLE_injective htle
  let r : Fin t → Set S := fun i => r₀ (emb i)
  let P : Fin t → Graph α β := fun i => P₀ (emb i)
  let Q : Fin t → Graph α β := fun i => Q₀ (emb i)
  have hri : Function.Injective r := hri₀.comp hemb
  have heye : ∀ i, IsEyeWithPaths G Γ η θ T (r i) (P i) (Q i) := fun i => heye₀ (emb i)
  have hfar : ∀ i j, i ≠ j → N ≤ d (r i) (r j) :=
    fun i j hij => hfar₀ (emb i) (emb j) (fun h => hij (hemb h))
  have hdisj : ∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
      ((P j).vertexSet ∪ (Q j).vertexSet) :=
    fun i j hij => hdisj₀ (emb i) (emb j) (fun h => hij (hemb h))
  have hex := fun i => (heye i).2
  choose C a b c d' hC hCG hCr ha hb hc hd hnodup horder hfree hPQ hP hQ using hex
  have hr : ∀ i, r i ∈ Γ.R := fun i => (heye i).1
  obtain ⟨ends, H, hinj, hends, hinc, hH, hHc, hHH, hclass, hp0, hp1⟩ :=
    hconnect Γ θ T d r C a b c d' hm.1.1 hm hN hr hri hfar hC hCG hCr
      (fun i => ⟨ha i, hb i, hc i, hd i⟩) horder hfree
  let R₀ : Fin t × Bool → Graph α β := fun x => if x.2 then Q x.1 else P x.1
  let s : Fin t × Bool → S := fun x => if x.2 then b x.1 else a x.1
  let z : Fin t × Bool → S := fun x => if x.2 then d' x.1 else c x.1
  have hR₀ : ∀ x, IsHPathWithEnds G η.imageGraph (R₀ x) (η.vMap (s x)) (η.vMap (z x)) := by
    rintro ⟨i, b'⟩
    cases b'
    · exact hP i
    · exact hQ i
  have hR₀R₀ : Pairwise (fun x y => Disjoint (R₀ x).vertexSet (R₀ y).vertexSet) := by
    rintro ⟨i, b'⟩ ⟨j, c'⟩ hneq
    by_cases hij : i = j
    · subst j
      cases b' <;> cases c'
      · exact False.elim (hneq rfl)
      · exact hPQ i
      · exact (hPQ i).symm
      · exact False.elim (hneq rfl)
    · have hi : (R₀ (i, b')).vertexSet ⊆ (P i).vertexSet ∪ (Q i).vertexSet := by
        cases b'
        · exact subset_union_left
        · exact subset_union_right
      have hj : (R₀ (j, c')).vertexSet ⊆ (P j).vertexSet ∪ (Q j).vertexSet := by
        cases c'
        · exact subset_union_left
        · exact subset_union_right
      exact (hdisj i j hij).mono hi hj
  have hpairs : ∀ x, ({ends (σ x, false), ends (σ x, true)} : Set S) = {s x, z x} := by
    rintro ⟨i, b'⟩
    cases b'
    · exact hp0 i
    · exact hp1 i
  obtain ⟨R, hR, hRR⟩ := exists_external_paths_reindexed η.vMap σ ends s z R₀ hR₀ hR₀R₀ hpairs
  have hEΓ : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hm.1.2.1 (by omega)
  have hcardW : Fintype.card W = Nat.card W := Nat.card_eq_fintype_card.symm
  have hfar' : ∀ i j, i ≠ j → 2 * Fintype.card W + 2 ≤ d (r i) (r j) := by
    intro i j hij
    rw [hcardW]
    exact (by omega : 2 * Nat.card W + 2 ≤ N).trans (hfar i j hij)
  have hθ : Fintype.card W ≤ θ := by rw [hcardW]; omega
  have hcL := controlsMinor_of_eye_connections hS η hm hCtrl hEΓ L κ σ hlink hκne htwo
    r hr hfar' hθ ends hends hinc H hH hHc hHH hclass R hR hRR
  obtain ⟨e, _⟩ := hEΓ
  let : Nonempty β := ⟨η.eMap e⟩
  exact theorem_4_2_proof hCtrl.isTangle_star.finite_V hCtrl.isTangle_star.finite_E
    (Set.toFinite L.vertexSet) (Set.toFinite L.edgeSet) hminor hcL

/-- XII (4.5), pages 252--253, for `p ≥ 4`, in the independent-eye
span formulation used by XV. The only statement hypotheses are
VII (7.5), (5.1), and (5.5). The paper reduces to `p ≥ 5`.
A larger threshold includes the source vertex-count bound
explicitly before applying the final separation estimate. -/
theorem theorem_4_5_span_large
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) (hp : 4 ≤ p) :
    ∃ k N : ℕ, 1 ≤ N ∧ ∀ {α β : Type*} (G : Graph α β) (θstar θ : ℕ)
      (Tstar : Set (Hypergraph α β × Hypergraph α β)) (Γ : Drawing S)
      (η : SpanEmbedding Γ G) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → N ≤ θ →
      ∀ (r : Fin k → Set S) (P Q : Fin k → Graph α β),
      Function.Injective r → (∀ i, IsEyeWithPaths G Γ η θ T (r i) (P i) (Q i)) →
      (∀ i j, i ≠ j → N ≤ d (r i) (r j)) →
      (∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
        ((P j).vertexSet ∪ (Q j).vertexSet)) →
      ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  obtain ⟨a₀, b₀, he⟩ := exists_closed_surface_model hS
  exact ⟨theorem_4_5_large_kBound p, theorem_4_5_large_NBound GM07.vModel a₀ b₀ p,
    (by unfold theorem_4_5_large_NBound; exact (by omega : 1 ≤ 2 * (p + 2 * theorem_4_5_large_kBound p) + 3).trans (le_max_right _ _)),
    theorem_4_5_span_large_explicit GM07.vModel (fun _ _ _ _ => le_rfl) hS he p hp⟩

end GraphMinor.GM12
