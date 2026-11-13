module

public import GraphMinor.Compute.Specs4
public import GraphMinor.Compute.Bridge13
public import GraphMinor.GM13.Section4
import GraphMinor.Compute.Join441
import GraphMinor.Compute.Algorithm101Defs

/-!
# The folio decision in Graph Minors XIII, (4.3)

Step (4), on page 77, tests the finite excluded-minor list against the unrooted
folio. Equal folios give the same answer for every graph in that list. This
file proves that fact and defines the finite lookup used by the RAM program.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor GM13 Set Graph Classical

/-- The unrooted folio written by (4.1), as used in Step (4) of XIII (4.3), page 77. -/
def IsEmptyFolio43 {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (F : FolioSetRep 0 δ) : Prop :=
  ∀ H : ComputeRootedDigraph 0, H.HasDetailLe δ →
    (F.MemIso H ↔ HasRootedDigraphModel H (G.toMultiComputeRootedDigraph []))

/-- An encoded folio determines its representation, including when its list is empty. -/
theorem folioSetRep_eq_of_enc_eq43 {δ : ℕ} {F₁ F₂ : FolioSetRep 0 δ}
    (h : encFolioSetRep F₁ = encFolioSetRep F₂) : F₁ = F₂ := by
  have hp := congrArg (parseFolioSetRep 0 δ) h
  have h₁ := parseFolioSetRep_encFolioSetRep F₁ []
  have h₂ := parseFolioSetRep_encFolioSetRep F₂ []
  simp only [List.append_nil] at h₁ h₂
  rw [h₁, h₂] at hp
  exact congrArg Prod.fst (Option.some.inj hp)

/-- Sharing the unrooted folio gives equality of folios relative to the empty root set,
even when the two graphs have different numbers of vertices. -/
theorem sameEmptyFolio43 {n₁ n₂ δ : ℕ} {G₁ : MultiDigraph n₁} {G₂ : MultiDigraph n₂}
    {F : FolioSetRep 0 δ} (h₁ : IsEmptyFolio43 δ G₁ F) (h₂ : IsEmptyFolio43 δ G₂ F) :
    HasSameDeltaFolioRel G₁.toGMDigraph G₂.toGMDigraph δ ∅ := by
  have hs : HasSameDeltaFolio (G₁.toGMRootedDigraph ∅) (G₂.toGMRootedDigraph ∅) δ := by
    apply (hasSameDeltaFolio_iff_forall_computeRootedDigraph _ _ δ).mpr
    intro H hH
    have hi₁ := hasRootedDigraphModel_iff_inFolio G₁ ∅ H
    have hi₂ := hasRootedDigraphModel_iff_inFolio G₂ ∅ H
    have hm₁ := hasRootedDigraphModel_rootedDigraphOfZ_empty_iff G₁ H
    have hm₂ := hasRootedDigraphModel_rootedDigraphOfZ_empty_iff G₂ H
    exact hi₁.symm.trans (hm₁.trans
      (((h₁ H hH).symm.trans (h₂ H hH)).trans (hm₂.symm.trans hi₂)))
  apply (hasSameDeltaFolioRel_iff_hasSameDeltaFolio_of_injective
    (empty_subset _) (empty_subset _)
    (v' := fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) (by simp)).mpr
  have he₁ : G₁.toGMRootedDigraph ∅ =
      (⟨G₁.toGMDigraph, (fun i : Fin 0 => Fin.elim0 i), (fun i => Fin.elim0 i)⟩ :
        RootedDigraph ℕ (ℕ × ℕ × ℕ) 0) := by
    unfold MultiDigraph.toGMRootedDigraph
    congr 1
    funext i
    have hi : i.1 < 0 := by simpa only [Finset.card_empty] using i.2
    omega
  have he₂ : G₂.toGMRootedDigraph ∅ =
      (⟨G₂.toGMDigraph, (fun i : Fin 0 => Fin.elim0 i), (fun i => Fin.elim0 i)⟩ :
        RootedDigraph ℕ (ℕ × ℕ × ℕ) 0) := by
    unfold MultiDigraph.toGMRootedDigraph
    congr 1
    funext i
    have hi : i.1 < 0 := by simpa only [Finset.card_empty] using i.2
    omega
  rw [he₁, he₂] at hs
  exact hs

/-- Step (4) of XIII (4.3), page 77: the finite excluded-minor list makes membership
constant on graphs with the same unrooted folio. The list and its bounds are the
local data obtained in the proof of (4.3). -/
theorem membership_iff_of_emptyFolio43
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ))) (B : Finset (Graph ℕ (ℕ × ℕ × ℕ))) (δ : ℕ)
    (hB : ∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ V(H).ncard ≤ δ ∧ E(H).ncard ≤ δ)
    (hclass : ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
      (G ∈ ℱ ↔ ∀ H ∈ B, ¬ IsIsoMinor H G))
    {n₁ n₂ : ℕ} {G₁ : MultiDigraph n₁} {G₂ : MultiDigraph n₂} {F : FolioSetRep 0 δ}
    (h₁ : IsEmptyFolio43 δ G₁ F) (h₂ : IsEmptyFolio43 δ G₂ F) :
    G₁.toGMDigraph.toGraph ∈ ℱ ↔ G₂.toGMDigraph.toGraph ∈ ℱ := by
  rw [hclass _ G₁.isFinite_toGMDigraph.finite_V G₁.isFinite_toGMDigraph.finite_E,
    hclass _ G₂.isFinite_toGMDigraph.finite_V G₂.isFinite_toGMDigraph.finite_E]
  apply forall₂_congr
  intro H hHB
  have hh := hB H hHB
  exact not_congr (isIsoMinor_iff_of_hasSameDeltaFolioRel_empty
    G₁.isFinite_toGMDigraph G₂.isFinite_toGMDigraph (sameEmptyFolio43 h₁ h₂)
    hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)

/-- A subgraph selected by (3.3) is a minor of the input graph. The minor map
is the identity on the subgraph's vertices and edges, with no edges contracted. -/
theorem isIsoMinor_of_multi_le43 {n : ℕ} {G' G : MultiDigraph n} (h : G' ≤ G) :
    IsIsoMinor G'.toGMDigraph.toGraph G.toGMDigraph.toGraph := by
  have hgraph : G'.toGMDigraph.toGraph ≤ G.toGMDigraph.toGraph := by
    refine ⟨Subset.rfl, ?_⟩
    intro e x y he
    rcases he with ⟨⟨hu, hv, he⟩, hends⟩
    exact ⟨⟨hu, hv, he.trans_le (h _ _)⟩, hends⟩
  obtain ⟨K, hK, C, hC, hIso⟩ := IsIsoMinor.refl G'.toGMDigraph.toGraph
  exact ⟨K, hK.trans hgraph, C, hC, hIso⟩

/-- The fixed class's answer for a written unrooted folio. Step (4) of XIII (4.3)
uses only the folio to decide membership. The RAM implementation expands this
function into a finite decision tree, so no membership query occurs at run time. -/
noncomputable def classFolioAnswer43
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ))) (δ : ℕ) (words : List ℕ) : ℕ := by
  classical
  exact if ∃ (n : ℕ) (G : MultiDigraph n) (F : FolioSetRep 0 δ),
    encFolioSetRep F = words ∧ IsEmptyFolio43 δ G F ∧ G.toGMDigraph.toGraph ∈ ℱ
    then 1 else 0

/-- The class lookup is a Boolean word on every prefix, including invalid folio prefixes. -/
theorem classFolioAnswer43_le_one (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ))) (δ : ℕ)
    (words : List ℕ) : classFolioAnswer43 ℱ δ words ≤ 1 := by
  classical
  unfold classFolioAnswer43
  split_ifs <;> omega

/-- The finite lookup gives the class's answer on every valid folio of the input graph. -/
theorem classFolioAnswer43_correct
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ))) (B : Finset (Graph ℕ (ℕ × ℕ × ℕ))) (δ : ℕ)
    (hB : ∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ V(H).ncard ≤ δ ∧ E(H).ncard ≤ δ)
    (hclass : ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
      (G ∈ ℱ ↔ ∀ H ∈ B, ¬ IsIsoMinor H G))
    {n : ℕ} {G : MultiDigraph n} {F : FolioSetRep 0 δ} (hF : IsEmptyFolio43 δ G F) :
    classFolioAnswer43 ℱ δ (encFolioSetRep F) =
      if G.toGMDigraph.toGraph ∈ ℱ then 1 else 0 := by
  classical
  have heq : (∃ (m : ℕ) (G' : MultiDigraph m) (F' : FolioSetRep 0 δ),
      encFolioSetRep F' = encFolioSetRep F ∧ IsEmptyFolio43 δ G' F' ∧
        G'.toGMDigraph.toGraph ∈ ℱ) ↔ G.toGMDigraph.toGraph ∈ ℱ := by
    constructor
    · rintro ⟨m, G', F', henc, hF', hmem⟩
      have hFF := folioSetRep_eq_of_enc_eq43 henc
      subst F'
      exact (membership_iff_of_emptyFolio43 ℱ B δ hB hclass hF' hF).mp hmem
    · intro hmem
      exact ⟨n, G, F, rfl, hF, hmem⟩
  simp only [classFolioAnswer43, heq]

end GraphMinor.Compute
