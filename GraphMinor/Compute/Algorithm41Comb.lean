module

public import GraphMinor.Compute.Algorithm41FolioOps
public import GraphMinor.Compute.BranchDecomp

/-!
# Certified Folio Tables and DP Transition Operators for GM XIII (4.1)

This file builds the certified dynamic programming table (`CertFolioTable`) and its base-case and
combination operators for Algorithm (4.1) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem* (pages 75–76):

1. **`CertFolioEntry` and `CertFolioTable`:** Bundles a representative rooted digraph `H` of
   detail `≤ δ` with a concrete model `PieceRootedModel G VA EA r H` as its certificate, proving
   that the resulting `FolioSetRep q δ` is sound and complete for the `δ`-folio of `(VA, EA)`
   relative to `r`.
2. **Combination step (`combineCertFolioTable`):** Implements Step (2) and Step (3) of Algorithm
   (4.1) by combining certified folio tables across a separation `(VA, EA)` and `(VB, EB)` using
   GM XIII (2.2) (`glueRootedDigraphs` and `PieceRootedModel.glue`) followed by GM XIII (2.1)
   (`restrictRootedDigraph` and `PieceRootedModel.restrict`), and proves soundness and completeness.
3. **Base step (`baseCertFolioTable`):** Implements Step (1) (and the leaf piece `A_m` in Step (3))
   by searching over subgraphs supported in `(VA, EA)` (`VA.powerset` and `EA.powerset`), and proves
   soundness and completeness.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Certified Folio Entries and Tables -/

/-- A certified entry in the `δ`-folio table of a piece `(VA, EA)` of `G` relative to roots `r`:
a `q`-rooted digraph `H` of detail `≤ δ` together with a concrete `PieceRootedModel G VA EA r H`. -/
structure CertFolioEntry {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (r : Fin q → Fin G.numVerts) (δ : ℕ) where
  /-- Representative `q`-rooted digraph `H`. -/
  H : ComputeRootedDigraph q
  /-- `H` has detail `≤ δ`. -/
  hdet : H.HasDetailLe δ
  /-- Concrete model of `H` in `(VA, EA)` relative to `r`. -/
  model : PieceRootedModel G VA EA r H

/-- Deduplicate a list of `CertFolioEntry` up to `IsRootedDigraphIso`, keeping one entry per
isomorphism class. -/
def dedupCertEntries {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ} :
    List (CertFolioEntry G VA EA r δ) → List (CertFolioEntry G VA EA r δ)
  | [] => []
  | e :: es =>
    if (dedupCertEntries es).any (fun e' => decide (IsRootedDigraphIso e.H e'.H)) then
      dedupCertEntries es
    else
      e :: dedupCertEntries es

theorem dedupCertEntries_sub {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ} :
    ∀ (es : List (CertFolioEntry G VA EA r δ)) {e : CertFolioEntry G VA EA r δ},
      e ∈ dedupCertEntries es → e ∈ es
  | [], _, he => by contradiction
  | a :: es, e, he => by
    unfold dedupCertEntries at he
    split_ifs at he with h
    · exact List.mem_cons_of_mem a (dedupCertEntries_sub es he)
    · rcases List.mem_cons.mp he with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (dedupCertEntries_sub es hmem)

theorem dedupCertEntries_pairwise {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ} :
    ∀ (es : List (CertFolioEntry G VA EA r δ)),
      ((dedupCertEntries es).map (fun e => encRootedDigraph e.H)).Pairwise
        (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode q c₁ c₂)
  | [] => List.Pairwise.nil
  | e :: es => by
    unfold dedupCertEntries
    split_ifs with h
    · exact dedupCertEntries_pairwise es
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun c' hc' hiso => h ?_, dedupCertEntries_pairwise es⟩
      rcases List.mem_map.mp hc' with ⟨e', he', rfl⟩
      rw [isIsoRootedDigraphCode_enc_iff] at hiso
      rw [List.any_eq_true]
      exact ⟨e', he', decide_eq_true hiso⟩

theorem exists_iso_dedupCertEntries {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ} :
    ∀ (es : List (CertFolioEntry G VA EA r δ)),
      ∀ e ∈ es, ∃ e' ∈ dedupCertEntries es, IsRootedDigraphIso e.H e'.H
  | [], e, he => by contradiction
  | a :: es, e, he => by
    unfold dedupCertEntries
    rcases List.mem_cons.mp he with rfl | hmem
    · split_ifs with h
      · rw [List.any_eq_true] at h
        rcases h with ⟨e', he', hiso⟩
        exact ⟨e', he', of_decide_eq_true hiso⟩
      · exact ⟨e, List.mem_cons_self, isRootedDigraphIso_refl e.H⟩
    · rcases exists_iso_dedupCertEntries es e hmem with ⟨e', he', hiso⟩
      split_ifs with h
      · exact ⟨e', he', hiso⟩
      · exact ⟨e', List.mem_cons_of_mem a he', hiso⟩

/-- A certified `δ`-folio table of a piece `(VA, EA)` of `G` relative to `r : Fin q → Fin G.numVerts`:
a list of pairwise non-isomorphic `CertFolioEntry`s that is complete for all `q`-rooted digraphs
of detail `≤ δ` having a `PieceRootedModel` in `(VA, EA)` relative to `r`. -/
structure CertFolioTable {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (r : Fin q → Fin G.numVerts) (δ : ℕ) where
  /-- Representative entries `(H, hdet, model)`. -/
  entries : List (CertFolioEntry G VA EA r δ)
  /-- Encoded rooted digraphs are pairwise non-isomorphic. -/
  pairwise_nonIso :
    (entries.map (fun e => encRootedDigraph e.H)).Pairwise
      (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode q c₁ c₂)
  /-- Completeness: every `H` of detail `≤ δ` with a model in `(VA, EA)` is isomorphic to some entry. -/
  complete :
    ∀ H : ComputeRootedDigraph q, H.HasDetailLe δ →
      HasPieceRootedModel G VA EA r H →
      ∃ e ∈ entries, IsRootedDigraphIso H e.H

/-- Extract the underlying `FolioSetRep q δ` of folio codes from a `CertFolioTable`. -/
def CertFolioTable.toFolioSetRep {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (T : CertFolioTable G VA EA r δ) : FolioSetRep q δ where
  codes := T.entries.map (fun e => encRootedDigraph e.H)
  all_detail := fun c hc => by
    rcases List.mem_map.mp hc with ⟨e, _, rfl⟩
    exact isDetailLeCode_encRootedDigraph e.hdet
  pairwise_nonIso := T.pairwise_nonIso

/-- Soundness and completeness of `T.toFolioSetRep`: for every `H : ComputeRootedDigraph q` with
detail `≤ δ`, `H` belongs (up to isomorphism) to `T.toFolioSetRep` if and only if `H` has a
`PieceRootedModel` in `(VA, EA)` relative to `r`. -/
theorem CertFolioTable.memIso_toFolioSetRep_iff {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (T : CertFolioTable G VA EA r δ) {H : ComputeRootedDigraph q} (hdet : H.HasDetailLe δ) :
    T.toFolioSetRep.MemIso H ↔ HasPieceRootedModel G VA EA r H := by
  unfold FolioSetRep.MemIso CertFolioTable.toFolioSetRep
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨e, _, rfl⟩, hiso⟩
    rw [isIsoRootedDigraphCode_enc_iff] at hiso
    exact (HasPieceRootedModel.iff_of_iso hiso).mpr ⟨e.model⟩
  · intro hmod
    rcases T.complete H hdet hmod with ⟨e, he, hiso⟩
    exact ⟨encRootedDigraph e.H, ⟨e, he, rfl⟩, (isIsoRootedDigraphCode_enc_iff H e.H).mpr hiso⟩

/-- Every `CertFolioTable` has at most `(allDetailLeCodes q δ).length` entries. -/
theorem CertFolioTable.length_entries_le {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (T : CertFolioTable G VA EA r δ) :
    T.entries.length ≤ (allDetailLeCodes q δ).length := by
  have hlen := length_codes_le_allDetailLeCodes T.toFolioSetRep
  simpa [CertFolioTable.toFolioSetRep] using hlen

/-! ### Section 2: Combination Step via GM XIII (2.2) and (2.1) -/

/-- Computable enumeration of all subsets of `S : Finset (Fin k)`. -/
def finsetSubsets {k : ℕ} (S : Finset (Fin k)) : List (Finset (Fin k)) :=
  (finsetToFinList S).sublists.map List.toFinset

@[simp]
theorem mem_finsetSubsets {k : ℕ} (S U : Finset (Fin k)) :
    U ∈ finsetSubsets S ↔ U ⊆ S := by
  unfold finsetSubsets
  rw [List.mem_map]
  constructor
  · rintro ⟨L, hL, rfl⟩
    intro x hx
    rw [List.mem_toFinset] at hx
    exact (mem_finsetToFinList S x).mp (List.Sublist.subset (List.mem_sublists.mp hL) hx)
  · intro hU
    refine ⟨(finsetToFinList S).filter (· ∈ U), List.mem_sublists.mpr (List.filter_sublist), ?_⟩
    ext x
    simp only [List.mem_toFinset, List.mem_filter, mem_finsetToFinList, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun hx => ⟨hU hx, hx⟩⟩

/-- Candidate entries generated from a single pair `(e_A, e_B)` by gluing via (2.2) and restricting
to all valid vertex subsets `U` via (2.1). -/
def combineEntryPair {q q_A q_B q' δ : ℕ} {G : ComputeDigraph}
    {VA VB : Finset (Fin G.numVerts)} {EA EB : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts}
    {α_A : Fin q_A → Fin q} {α_B : Fin q_B → Fin q}
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (hE_disj : Disjoint EA EB)
    (hsep_inter : ∀ w ∈ VA ∩ VB, ∃ (i_A : Fin q_A) (i_B : Fin q_B),
      α_A i_A = α_B i_B ∧ r (α_A i_A) = w)
    (β : Fin q' → Fin q)
    (e_A : CertFolioEntry G VA EA (r ∘ α_A) δ)
    (e_B : CertFolioEntry G VB EB (r ∘ α_B) δ) :
    List (CertFolioEntry G (VA ∪ VB) (EA ∪ EB) (r ∘ β) δ) :=
  let H_AB := glueRootedDigraphs α_A α_B hcov e_A.H e_B.H
  let M_AB := PieceRootedModel.glue hcov hE_disj hsep_inter e_A.model e_B.model
  (finsetSubsets (Finset.univ : Finset (Fin H_AB.digraph.numVerts))).filterMap (fun U =>
    if hU : IsValidRootedSubverts H_AB β U then
      let H' := restrictRootedDigraph H_AB β U hU
      if hdet' : H'.HasDetailLe δ then
        some {
          H := H'
          hdet := hdet'
          model := M_AB.restrict β U hU
        }
      else
        none
    else
      none)

/-- **Combination step of GM XIII (4.1) (Steps (2) and (3), page 76):**
Combines a certified folio table `T_A` for `(VA, EA, r ∘ α_A)` and a certified folio table `T_B`
for `(VB, EB, r ∘ α_B)` into a certified folio table for `(VA ∪ VB, EA ∪ EB, r ∘ β)` by applying
GM XIII (2.2) (`glueRootedDigraphs`) and GM XIII (2.1) (`restrictRootedDigraph`) in constant time. -/
def combineCertFolioTable {q q_A q_B q' δ : ℕ} {G : ComputeDigraph}
    {VA VB : Finset (Fin G.numVerts)} {EA EB : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts}
    {α_A : Fin q_A → Fin q} {α_B : Fin q_B → Fin q}
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (hE_disj : Disjoint EA EB)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    (hEB : ∀ e ∈ EB, G.head e ∈ VB ∧ G.tail e ∈ VB)
    (hrA : ∀ i_A : Fin q_A, r (α_A i_A) ∈ VA)
    (hrB : ∀ i_B : Fin q_B, r (α_B i_B) ∈ VB)
    (hsep : ∀ x ∈ VA, x ∈ VB → ∃ i_A i_B, α_A i_A = α_B i_B ∧ r (α_A i_A) = x)
    (β : Fin q' → Fin q)
    (T_A : CertFolioTable G VA EA (r ∘ α_A) δ)
    (T_B : CertFolioTable G VB EB (r ∘ α_B) δ) :
    CertFolioTable G (VA ∪ VB) (EA ∪ EB) (r ∘ β) δ :=
  have hsep_inter : ∀ w ∈ VA ∩ VB, ∃ (i_A : Fin q_A) (i_B : Fin q_B),
      α_A i_A = α_B i_B ∧ r (α_A i_A) = w := by
    intro w hw
    exact hsep w (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
  have hr_AB : ∀ j : Fin q, r j ∈ VA ∪ VB := by
    intro j
    rcases hcov j with ⟨i_A, rfl⟩ | ⟨i_B, rfl⟩
    · exact Finset.mem_union_left _ (hrA i_A)
    · exact Finset.mem_union_right _ (hrB i_B)
  let candidates := T_A.entries.flatMap (fun e_A =>
    T_B.entries.flatMap (fun e_B =>
      combineEntryPair hcov hE_disj hsep_inter β e_A e_B))
  {
    entries := dedupCertEntries candidates
    pairwise_nonIso := dedupCertEntries_pairwise candidates
    complete := fun H_target hdet_target ⟨M_target⟩ => by
      -- Step 1: Extend `H_target` from `r ∘ β` to `r` via completeness of (2.1).
      rcases exists_extend_of_pieceRootedModel hr_AB β hdet_target M_target with
        ⟨H_ext, hdet_ext, M_ext, U_ext, hU_ext, hiso_ext⟩
      -- Step 2: Split `(H_ext, M_ext)` across `(VA, EA)` and `(VB, EB)` via completeness of (2.2).
      rcases exists_split_of_pieceRootedModel α_A α_B hcov hE_disj hEA hEB hrA hrB hsep
          hdet_ext M_ext with
        ⟨H_A0, H_B0, hdet_A0, hdet_B0, ⟨M_A0⟩, ⟨M_B0⟩, hiso_glue0⟩
      -- Step 3: Lookup `H_A0` in `T_A` and `H_B0` in `T_B`.
      rcases T_A.complete H_A0 hdet_A0 ⟨M_A0⟩ with ⟨e_A, he_A, ⟨iso_A⟩⟩
      rcases T_B.complete H_B0 hdet_B0 ⟨M_B0⟩ with ⟨e_B, he_B, ⟨iso_B⟩⟩
      -- Step 4: By isomorphism invariance of `glueRootedDigraphs`, `H_ext` is isomorphic to
      -- `glueRootedDigraphs α_A α_B hcov e_A.H e_B.H`.
      have hiso_glue_rep :
          IsRootedDigraphIso
            (glueRootedDigraphs α_A α_B hcov H_A0 H_B0)
            (glueRootedDigraphs α_A α_B hcov e_A.H e_B.H) :=
        isRootedDigraphIso_glueRootedDigraphs α_A α_B hcov iso_A iso_B
      rcases isRootedDigraphIso_trans (isRootedDigraphIso_symm hiso_glue0) hiso_glue_rep with
        ⟨iso_ext_AB⟩
      -- Step 5: Transport `U_ext` along `iso_ext_AB` via `restrictRootedDigraphIso`.
      let H_AB := glueRootedDigraphs α_A α_B hcov e_A.H e_B.H
      let U_AB : Finset (Fin H_AB.digraph.numVerts) := U_ext.map iso_ext_AB.vertEquiv.toEmbedding
      have hU_AB : IsValidRootedSubverts H_AB β U_AB := by
        refine ⟨fun i => ?_, fun e => ?_⟩
        · rw [Finset.mem_map, ← iso_ext_AB.map_roots (β i)]
          exact ⟨H_ext.roots (β i), hU_ext.1 i, rfl⟩
        · obtain ⟨e₁, rfl⟩ := iso_ext_AB.edgeEquiv.surjective e
          rw [iso_ext_AB.map_head e₁, iso_ext_AB.map_tail e₁, Finset.mem_map, Finset.mem_map]
          exact ⟨⟨H_ext.digraph.head e₁, (hU_ext.2 e₁).1, rfl⟩,
                 ⟨H_ext.digraph.tail e₁, (hU_ext.2 e₁).2, rfl⟩⟩
      have hiso_rest :
          IsRootedDigraphIso
            (restrictRootedDigraph H_ext β U_ext hU_ext)
            (restrictRootedDigraph H_AB β U_AB hU_AB) :=
        ⟨restrictRootedDigraphIso iso_ext_AB β U_ext hU_ext⟩
      have hiso_target_AB :
          IsRootedDigraphIso H_target (restrictRootedDigraph H_AB β U_AB hU_AB) :=
        isRootedDigraphIso_trans (isRootedDigraphIso_symm hiso_ext) hiso_rest
      rcases hiso_target_AB with ⟨iso_t⟩
      have hdet_AB' : (restrictRootedDigraph H_AB β U_AB hU_AB).HasDetailLe δ :=
        HasDetailLe.of_iso iso_t hdet_target
      -- Step 6: Show the candidate entry is in `candidates`, hence represented in `dedupCertEntries`.
      let M_AB := PieceRootedModel.glue hcov hE_disj hsep_inter e_A.model e_B.model
      let cand : CertFolioEntry G (VA ∪ VB) (EA ∪ EB) (r ∘ β) δ := {
        H := restrictRootedDigraph H_AB β U_AB hU_AB
        hdet := hdet_AB'
        model := M_AB.restrict β U_AB hU_AB
      }
      have hcand_mem : cand ∈ candidates := by
        dsimp [candidates]
        rw [List.mem_flatMap]
        refine ⟨e_A, he_A, ?_⟩
        rw [List.mem_flatMap]
        refine ⟨e_B, he_B, ?_⟩
        unfold combineEntryPair
        rw [List.mem_filterMap]
        refine ⟨U_AB, by simp, ?_⟩
        simp [hU_AB, hdet_AB', cand, H_AB, M_AB]
      rcases exists_iso_dedupCertEntries candidates cand hcand_mem with ⟨e_final, he_final, hiso_f⟩
      exact ⟨e_final, he_final, isRootedDigraphIso_trans ⟨iso_t⟩ hiso_f⟩
  }

/-! ### Section 3: Base Step for Small Pieces `(VA, EA)` -/

instance instDecidableIsNonNullConnected {G : ComputeDigraph} (S : DigraphSubgraph G) :
    Decidable S.IsNonNullConnected :=
  inferInstanceAs
    (Decidable (S.verts.Nonempty ∧
      ∀ u ∈ S.verts, ∀ v ∈ S.verts, S.underlyingSimpleGraph.Reachable u v))

/-- Construct a `DigraphSubgraph G` from `(V, E)` given the endpoint proof `h`. -/
def mkPieceSubgraph {G : ComputeDigraph}
    (V : Finset (Fin G.numVerts)) (E : Finset (Fin G.numEdges))
    (h : ∀ e ∈ E, G.head e ∈ V ∧ G.tail e ∈ V) : DigraphSubgraph G where
  verts := V
  edges := E
  head_mem {_} he := (h _ he).1
  tail_mem {_} he := (h _ he).2

/-- Computable list of all non-null connected subgraphs `S : DigraphSubgraph G` supported in
`(VA, EA)`. When `|VA| ≤ 2` and `|EA| ≤ 1`, this list has length `≤ 8`. -/
def pieceSubgraphs (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges)) :
    List (DigraphSubgraph G) :=
  ((finsetSubsets VA).flatMap (fun V =>
    (finsetSubsets EA).filterMap (fun E =>
      if h : ∀ e ∈ E, G.head e ∈ V ∧ G.tail e ∈ V then
        if (mkPieceSubgraph V E h).IsNonNullConnected then
          some (mkPieceSubgraph V E h)
        else
          none
      else
        none)))

theorem mem_pieceSubgraphs_iff {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    (S : DigraphSubgraph G) :
    S ∈ pieceSubgraphs G VA EA ↔
      S.verts ⊆ VA ∧ S.edges ⊆ EA ∧ S.IsNonNullConnected := by
  unfold pieceSubgraphs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨V, hV, hE_mem⟩
    rw [mem_finsetSubsets] at hV
    rw [List.mem_filterMap] at hE_mem
    rcases hE_mem with ⟨E, hE, hopt⟩
    rw [mem_finsetSubsets] at hE
    split_ifs at hopt with hends hconn
    injection hopt with hS
    subst hS
    exact ⟨hV, hE, hconn⟩
  · rintro ⟨hV, hE, hconn⟩
    refine ⟨S.verts, by simp [hV], ?_⟩
    rw [List.mem_filterMap]
    refine ⟨S.edges, by simp [hE], ?_⟩
    have hends : ∀ e ∈ S.edges, G.head e ∈ S.verts ∧ G.tail e ∈ S.verts :=
      fun e he => ⟨S.head_mem he, S.tail_mem he⟩
    have hconn' : (mkPieceSubgraph S.verts S.edges hends).IsNonNullConnected := by
      have heq : mkPieceSubgraph S.verts S.edges hends = S := by cases S; rfl
      rwa [heq]
    split_ifs
    exact congrArg some (by cases S; rfl)

/-- Enumerate all functions `Fin m → α` whose values lie in `elems : List α`. -/
def allFinMaps {α : Type*} : (m : ℕ) → List α → List (Fin m → α)
  | 0, _ => [fun i => i.elim0]
  | m + 1, elems =>
    elems.flatMap (fun a =>
      (allFinMaps m elems).map (fun f => Fin.cases a f))

theorem exists_mem_allFinMaps {α : Type*} :
    ∀ (m : ℕ) (elems : List α) (f : Fin m → α),
      (∀ i : Fin m, f i ∈ elems) →
      ∃ g ∈ allFinMaps m elems, ∀ i : Fin m, g i = f i
  | 0, _, f, _ => ⟨fun i => i.elim0, by simp [allFinMaps], fun i => i.elim0⟩
  | m + 1, elems, f, hall => by
    rcases exists_mem_allFinMaps m elems (fun i => f i.succ) (fun i => hall i.succ) with
      ⟨g, hg_mem, hg_eq⟩
    refine ⟨Fin.cases (f 0) g, ?_, ?_⟩
    · simp only [allFinMaps, List.mem_flatMap, List.mem_map]
      exact ⟨f 0, hall 0, g, hg_mem, rfl⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        simpa using hg_eq j

/-- Check whether a candidate `(vertMap, edgeMap)` satisfies the conditions of a
`PieceRootedModel G VA EA r H` and construct it if so. -/
def buildPieceRootedModel? {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (r : Fin q → Fin G.numVerts) (H : ComputeRootedDigraph q)
    (vertMap : Fin H.digraph.numVerts → DigraphSubgraph G)
    (edgeMap : Fin H.digraph.numEdges → Fin G.numEdges) :
    Option (PieceRootedModel G VA EA r H) :=
  if hconn : ∀ v : Fin H.digraph.numVerts, (vertMap v).IsNonNullConnected then
  if hdisj : ∀ u v : Fin H.digraph.numVerts, u ≠ v → Disjoint (vertMap u).verts (vertMap v).verts then
  if hinj : Function.Injective edgeMap then
  if hnotMem : ∀ (v : Fin H.digraph.numVerts) (e : Fin H.digraph.numEdges),
      edgeMap e ∉ (vertMap v).edges then
  if hhead : ∀ e : Fin H.digraph.numEdges,
      G.head (edgeMap e) ∈ (vertMap (H.digraph.head e)).verts then
  if htail : ∀ e : Fin H.digraph.numEdges,
      G.tail (edgeMap e) ∈ (vertMap (H.digraph.tail e)).verts then
  if hroot : ∀ i : Fin q, r i ∈ (vertMap (H.roots i)).verts then
  if hvsub : ∀ v : Fin H.digraph.numVerts, (vertMap v).verts ⊆ VA then
  if hesub : ∀ v : Fin H.digraph.numVerts, (vertMap v).edges ⊆ EA then
  if hemem : ∀ e : Fin H.digraph.numEdges, edgeMap e ∈ EA then
    some {
      vertMap := vertMap
      edgeMap := edgeMap
      connected := hconn
      vert_disjoint := hdisj
      edge_injective := hinj
      edge_notMem_vert := hnotMem
      head_mem_vertMap := hhead
      tail_mem_vertMap := htail
      root_mem_vertMap := hroot
      verts_sub := hvsub
      vert_edges_sub := hesub
      edge_mem := hemem
    }
  else none else none else none else none else none
  else none else none else none else none else none

theorem buildPieceRootedModel?_isSome_of_model {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {H : ComputeRootedDigraph q}
    (M : PieceRootedModel G VA EA r H)
    {vertMap : Fin H.digraph.numVerts → DigraphSubgraph G}
    {edgeMap : Fin H.digraph.numEdges → Fin G.numEdges}
    (hv : ∀ u, vertMap u = M.vertMap u)
    (he : ∀ e, edgeMap e = M.edgeMap e) :
    (buildPieceRootedModel? G VA EA r H vertMap edgeMap).isSome = true := by
  have hv_eq : vertMap = M.vertMap := funext hv
  have he_eq : edgeMap = M.edgeMap := funext he
  subst hv_eq he_eq
  unfold buildPieceRootedModel?
  have h1 : ∀ v : Fin H.digraph.numVerts, (M.vertMap v).IsNonNullConnected := M.connected
  have h2 : ∀ u v : Fin H.digraph.numVerts,
      u ≠ v → Disjoint (M.vertMap u).verts (M.vertMap v).verts := M.vert_disjoint
  have h3 : Function.Injective M.edgeMap := M.edge_injective
  have h4 : ∀ (v : Fin H.digraph.numVerts) (e : Fin H.digraph.numEdges),
      M.edgeMap e ∉ (M.vertMap v).edges := M.edge_notMem_vert
  have h5 : ∀ e : Fin H.digraph.numEdges,
      G.head (M.edgeMap e) ∈ (M.vertMap (H.digraph.head e)).verts := M.head_mem_vertMap
  have h6 : ∀ e : Fin H.digraph.numEdges,
      G.tail (M.edgeMap e) ∈ (M.vertMap (H.digraph.tail e)).verts := M.tail_mem_vertMap
  have h7 : ∀ i : Fin q, r i ∈ (M.vertMap (H.roots i)).verts := M.root_mem_vertMap
  have h8 : ∀ v : Fin H.digraph.numVerts, (M.vertMap v).verts ⊆ VA := M.verts_sub
  have h9 : ∀ v : Fin H.digraph.numVerts, (M.vertMap v).edges ⊆ EA := M.vert_edges_sub
  have h10 : ∀ e : Fin H.digraph.numEdges, M.edgeMap e ∈ EA := M.edge_mem
  split_ifs <;> rfl

/-- Computable search for a `PieceRootedModel G VA EA r H` supported in `(VA, EA)`. -/
def findPieceRootedModel {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (r : Fin q → Fin G.numVerts) (H : ComputeRootedDigraph q) :
    Option (PieceRootedModel G VA EA r H) :=
  let subs := pieceSubgraphs G VA EA
  let vMaps := allFinMaps H.digraph.numVerts subs
  let eMaps := allFinMaps H.digraph.numEdges (finsetToFinList EA)
  (vMaps.flatMap (fun vm =>
    eMaps.filterMap (fun em =>
      buildPieceRootedModel? G VA EA r H vm em))).head?

theorem findPieceRootedModel_isSome_iff {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (r : Fin q → Fin G.numVerts) (H : ComputeRootedDigraph q) :
    (findPieceRootedModel G VA EA r H).isSome ↔ HasPieceRootedModel G VA EA r H := by
  unfold findPieceRootedModel
  constructor
  · intro h
    rcases Option.isSome_iff_exists.mp h with ⟨M, _⟩
    exact ⟨M⟩
  · rintro ⟨M⟩
    have hvm : ∀ u : Fin H.digraph.numVerts, M.vertMap u ∈ pieceSubgraphs G VA EA := by
      intro u
      rw [mem_pieceSubgraphs_iff]
      exact ⟨M.verts_sub u, M.vert_edges_sub u, M.connected u⟩
    have hem : ∀ e : Fin H.digraph.numEdges, M.edgeMap e ∈ finsetToFinList EA := by
      intro e
      rw [mem_finsetToFinList]
      exact M.edge_mem e
    rcases exists_mem_allFinMaps H.digraph.numVerts (pieceSubgraphs G VA EA) M.vertMap hvm with
      ⟨vm, hvm_mem, hvm_eq⟩
    rcases exists_mem_allFinMaps H.digraph.numEdges (finsetToFinList EA) M.edgeMap hem with
      ⟨em, hem_mem, hem_eq⟩
    rcases Option.isSome_iff_exists.mp
        (buildPieceRootedModel?_isSome_of_model M hvm_eq hem_eq) with ⟨M', hM'⟩
    let L := (allFinMaps H.digraph.numVerts (pieceSubgraphs G VA EA)).flatMap (fun vm =>
      (allFinMaps H.digraph.numEdges (finsetToFinList EA)).filterMap (fun em =>
        buildPieceRootedModel? G VA EA r H vm em))
    have hmem_list : M' ∈ L := by
      dsimp [L]
      rw [List.mem_flatMap]
      refine ⟨vm, hvm_mem, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨em, hem_mem, hM'⟩
    change L.head?.isSome = true
    cases hL : L with
    | nil =>
      rw [hL] at hmem_list
      cases hmem_list
    | cons hd tl =>
      rfl

/-- **Base step of GM XIII (4.1) (Step (1), page 76):**
Constructs the certified `δ`-folio table for a piece `(VA, EA)` relative to `r : Fin q → Fin G.numVerts`
by testing each representative rooted digraph code of detail `≤ δ` with `findPieceRootedModel`. -/
def baseCertFolioTable {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (r : Fin q → Fin G.numVerts) (δ : ℕ) :
    CertFolioTable G VA EA r δ :=
  let candidates : List (CertFolioEntry G VA EA r δ) :=
    (allDetailLeCodes q δ).filterMap (fun c =>
      match decRootedDigraph q c with
      | some H =>
        if hdet : H.HasDetailLe δ then
          match findPieceRootedModel G VA EA r H with
          | some M => some { H := H, hdet := hdet, model := M }
          | none => none
        else
          none
      | none => none)
  {
    entries := dedupCertEntries candidates
    pairwise_nonIso := dedupCertEntries_pairwise candidates
    complete := fun H hdet hmod => by
      have hsome := (findPieceRootedModel_isSome_iff G VA EA r H).mpr hmod
      rcases Option.isSome_iff_exists.mp hsome with ⟨M, hM⟩
      let cand : CertFolioEntry G VA EA r δ := { H := H, hdet := hdet, model := M }
      have hcand_mem : cand ∈ candidates := by
        dsimp [candidates]
        rw [List.mem_filterMap]
        refine ⟨encRootedDigraph H, ?_, ?_⟩
        · rw [mem_allDetailLeCodes_iff]
          exact isDetailLeCode_encRootedDigraph hdet
        · simp [decRootedDigraph_encRootedDigraph, hdet, hM, cand]
      rcases exists_iso_dedupCertEntries candidates cand hcand_mem with ⟨e', he', hiso⟩
      exact ⟨e', he', hiso⟩
  }

/-! ### Section 4: Branch-Decomposition Dynamic Programming of GM XIII (4.1) -/

/-- Canonical injective root map `Fin S.card → Fin n` enumerating `S : Finset (Fin n)` in
increasing order via `finsetEnumEquiv S`. -/
def finsetRootFn {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) : Fin n :=
  (finsetEnumEquiv S i).1

theorem finsetRootFn_mem {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) :
    finsetRootFn S i ∈ S :=
  (finsetEnumEquiv S i).2

theorem finsetRootFn_injective {n : ℕ} (S : Finset (Fin n)) :
    Function.Injective (finsetRootFn S) := by
  intro i j h
  exact (finsetEnumEquiv S).injective (Subtype.ext h)

theorem exists_finsetRootFn_eq {n : ℕ} {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) :
    ∃ i : Fin S.card, finsetRootFn S i = v :=
  ⟨(finsetEnumEquiv S).symm ⟨v, hv⟩,
   congrArg Subtype.val ((finsetEnumEquiv S).apply_symm_apply ⟨v, hv⟩)⟩

/-- Given `hsub : S₁ ⊆ S₂`, the canonical embedding `Fin S₁.card → Fin S₂.card` compatible with
`finsetRootFn`. -/
def finsetSubIdx {n : ℕ} {S₁ S₂ : Finset (Fin n)} (hsub : S₁ ⊆ S₂) (i : Fin S₁.card) :
    Fin S₂.card :=
  (finsetEnumEquiv S₂).symm ⟨finsetRootFn S₁ i, hsub (finsetRootFn_mem S₁ i)⟩

@[simp]
theorem finsetRootFn_comp_finsetSubIdx {n : ℕ} {S₁ S₂ : Finset (Fin n)} (hsub : S₁ ⊆ S₂) :
    finsetRootFn S₂ ∘ finsetSubIdx hsub = finsetRootFn S₁ := by
  funext i
  dsimp [finsetSubIdx, finsetRootFn]
  exact congrArg Subtype.val ((finsetEnumEquiv S₂).apply_symm_apply _)

@[simp]
theorem finsetRootFn_finsetSubIdx_apply {n : ℕ} {S₁ S₂ : Finset (Fin n)} (hsub : S₁ ⊆ S₂)
    (i : Fin S₁.card) :
    finsetRootFn S₂ (finsetSubIdx hsub i) = finsetRootFn S₁ i :=
  congrFun (finsetRootFn_comp_finsetSubIdx hsub) i

/-- Transport a `CertFolioTable G VA₁ EA₁ (finsetRootFn Z₁) δ` along set equalities
`hV : VA₁ = VA₂`, `hE : EA₁ = EA₂`, `hZ : Z₁ = Z₂`. -/
def CertFolioTable.castSets {G : ComputeDigraph}
    {VA₁ VA₂ : Finset (Fin G.numVerts)} {EA₁ EA₂ : Finset (Fin G.numEdges)}
    {Z₁ Z₂ : Finset (Fin G.numVerts)} {δ : ℕ}
    (hV : VA₁ = VA₂) (hE : EA₁ = EA₂) (hZ : Z₁ = Z₂)
    (T : CertFolioTable G VA₁ EA₁ (finsetRootFn Z₁) δ) :
    CertFolioTable G VA₂ EA₂ (finsetRootFn Z₂) δ :=
  hV ▸ hE ▸ hZ ▸ T

/-- High-level combination of two certified folio tables `T_A` (on `(VA, EA)` relative to `ZA`) and
`T_B` (on `(VB, EB)` relative to `ZB`) into a certified folio table on `(VA ∪ VB, EA ∪ EB)` relative
to `Z' ⊆ ZA ∪ ZB`, when `VA ∩ VB ⊆ ZA ∩ ZB` (GM XIII (4.1) Steps (2) and (3), page 76). -/
def combinePieceTables {G : ComputeDigraph}
    {VA VB ZA ZB Z' : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)} {δ : ℕ}
    (hZA : ZA ⊆ VA) (hZB : ZB ⊆ VB) (hZ' : Z' ⊆ ZA ∪ ZB)
    (hE_disj : Disjoint EA EB)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    (hEB : ∀ e ∈ EB, G.head e ∈ VB ∧ G.tail e ∈ VB)
    (hinter : VA ∩ VB ⊆ ZA ∩ ZB)
    (T_A : CertFolioTable G VA EA (finsetRootFn ZA) δ)
    (T_B : CertFolioTable G VB EB (finsetRootFn ZB) δ) :
    CertFolioTable G (VA ∪ VB) (EA ∪ EB) (finsetRootFn Z') δ :=
  let α_A := finsetSubIdx (Finset.subset_union_left : ZA ⊆ ZA ∪ ZB)
  let α_B := finsetSubIdx (Finset.subset_union_right : ZB ⊆ ZA ∪ ZB)
  let β := finsetSubIdx hZ'
  have hcov : ∀ k : Fin (ZA ∪ ZB).card, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k) := by
    intro k
    rcases Finset.mem_union.mp (finsetRootFn_mem (ZA ∪ ZB) k) with hkA | hkB
    · rcases exists_finsetRootFn_eq hkA with ⟨i_A, hi_A⟩
      left
      refine ⟨i_A, finsetRootFn_injective (ZA ∪ ZB) ?_⟩
      simpa [α_A] using hi_A
    · rcases exists_finsetRootFn_eq hkB with ⟨i_B, hi_B⟩
      right
      refine ⟨i_B, finsetRootFn_injective (ZA ∪ ZB) ?_⟩
      simpa [α_B] using hi_B
  have hrA : ∀ i_A : Fin ZA.card, finsetRootFn (ZA ∪ ZB) (α_A i_A) ∈ VA := by
    intro i_A
    rw [finsetRootFn_finsetSubIdx_apply]
    exact hZA (finsetRootFn_mem ZA i_A)
  have hrB : ∀ i_B : Fin ZB.card, finsetRootFn (ZA ∪ ZB) (α_B i_B) ∈ VB := by
    intro i_B
    rw [finsetRootFn_finsetSubIdx_apply]
    exact hZB (finsetRootFn_mem ZB i_B)
  have hsep : ∀ x ∈ VA, x ∈ VB →
      ∃ i_A i_B, α_A i_A = α_B i_B ∧ finsetRootFn (ZA ∪ ZB) (α_A i_A) = x := by
    intro x hxA hxB
    have hx_inter : x ∈ ZA ∩ ZB := hinter (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
    rcases exists_finsetRootFn_eq (Finset.mem_inter.mp hx_inter).1 with ⟨i_A, hi_A⟩
    rcases exists_finsetRootFn_eq (Finset.mem_inter.mp hx_inter).2 with ⟨i_B, hi_B⟩
    have hαA : finsetRootFn (ZA ∪ ZB) (α_A i_A) = x := by simpa [α_A] using hi_A
    have hαB : finsetRootFn (ZA ∪ ZB) (α_B i_B) = x := by simpa [α_B] using hi_B
    exact ⟨i_A, i_B, finsetRootFn_injective (ZA ∪ ZB) (hαA.trans hαB.symm), hαA⟩
  have hTA_eq : finsetRootFn (ZA ∪ ZB) ∘ α_A = finsetRootFn ZA :=
    finsetRootFn_comp_finsetSubIdx _
  have hTB_eq : finsetRootFn (ZA ∪ ZB) ∘ α_B = finsetRootFn ZB :=
    finsetRootFn_comp_finsetSubIdx _
  have hβ_eq : finsetRootFn (ZA ∪ ZB) ∘ β = finsetRootFn Z' :=
    finsetRootFn_comp_finsetSubIdx _
  hβ_eq ▸ combineCertFolioTable hcov hE_disj hEA hEB hrA hrB hsep β
    (hTA_eq.symm ▸ T_A) (hTB_eq.symm ▸ T_B)

/-- Whether vertex `w` is an endpoint of edge `e` in `G`. -/
def digraphIncident (G : ComputeDigraph) (w : Fin G.numVerts) (e : Fin G.numEdges) : Prop :=
  G.head e = w ∨ G.tail e = w

instance instDecidableDigraphIncident (G : ComputeDigraph)
    (w : Fin G.numVerts) (e : Fin G.numEdges) : Decidable (digraphIncident G w e) := by
  unfold digraphIncident
  infer_instance

/-- The set of vertices of `G` incident with at least one edge in `E`. -/
def edgeEnds (G : ComputeDigraph) (E : Finset (Fin G.numEdges)) : Finset (Fin G.numVerts) :=
  Finset.univ.filter (fun w => ∃ e ∈ E, digraphIncident G w e)

@[simp]
theorem mem_edgeEnds {G : ComputeDigraph} {E : Finset (Fin G.numEdges)} {w : Fin G.numVerts} :
    w ∈ edgeEnds G E ↔ ∃ e ∈ E, digraphIncident G w e := by
  simp [edgeEnds]

theorem head_mem_edgeEnds {G : ComputeDigraph} {E : Finset (Fin G.numEdges)}
    {e : Fin G.numEdges} (he : e ∈ E) : G.head e ∈ edgeEnds G E :=
  mem_edgeEnds.mpr ⟨e, he, Or.inl rfl⟩

theorem tail_mem_edgeEnds {G : ComputeDigraph} {E : Finset (Fin G.numEdges)}
    {e : Fin G.numEdges} (he : e ∈ E) : G.tail e ∈ edgeEnds G E :=
  mem_edgeEnds.mpr ⟨e, he, Or.inr rfl⟩

theorem edgeEnds_mono {G : ComputeDigraph} {E₁ E₂ : Finset (Fin G.numEdges)} (h : E₁ ⊆ E₂) :
    edgeEnds G E₁ ⊆ edgeEnds G E₂ := by
  intro w hw
  rcases mem_edgeEnds.mp hw with ⟨e, he, hinc⟩
  exact mem_edgeEnds.mpr ⟨e, h he, hinc⟩

@[simp]
theorem edgeEnds_empty (G : ComputeDigraph) : edgeEnds G ∅ = ∅ := by
  ext w
  simp

@[simp]
theorem edgeEnds_union (G : ComputeDigraph) (E₁ E₂ : Finset (Fin G.numEdges)) :
    edgeEnds G (E₁ ∪ E₂) = edgeEnds G E₁ ∪ edgeEnds G E₂ := by
  ext w
  simp only [mem_edgeEnds, Finset.mem_union]
  constructor
  · rintro ⟨e, he₁ | he₂, hinc⟩
    · exact Or.inl ⟨e, he₁, hinc⟩
    · exact Or.inr ⟨e, he₂, hinc⟩
  · rintro (⟨e, he₁, hinc⟩ | ⟨e, he₂, hinc⟩)
    · exact ⟨e, Or.inl he₁, hinc⟩
    · exact ⟨e, Or.inr he₂, hinc⟩

/-- For an edge subset `E ⊆ E(G)`, the vertex set `V(B) = edgeEnds G E` formed by the ends of `E`. -/
abbrev pieceVB (G : ComputeDigraph) (E : Finset (Fin G.numEdges)) : Finset (Fin G.numVerts) :=
  edgeEnds G E

/-- For an edge subset `E ⊆ E(G)`, the complementary vertex set `V(A) = edgeEnds G (E(G) \ E)`. -/
abbrev pieceVA (G : ComputeDigraph) (E : Finset (Fin G.numEdges)) : Finset (Fin G.numVerts) :=
  edgeEnds G (Finset.univ \ E)

/-- For an edge subset `E ⊆ E(G)` and root set `Z ⊆ V(G)`, the boundary root set
`Z_E = (V(A) ∪ Z) ∩ V(B)` (GM XIII (4.1), page 75). -/
abbrev pieceZ (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (E : Finset (Fin G.numEdges)) :
    Finset (Fin G.numVerts) :=
  (pieceVA G E ∪ Z) ∩ pieceVB G E

theorem pieceZ_subset_pieceVB (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (E : Finset (Fin G.numEdges)) :
    pieceZ G Z E ⊆ pieceVB G E :=
  Finset.inter_subset_right

theorem pieceVB_inter_subset_pieceZ {G : ComputeDigraph} (Z : Finset (Fin G.numVerts))
    {E₁ E₂ : Finset (Fin G.numEdges)} (hdisj : Disjoint E₁ E₂) :
    pieceVB G E₁ ∩ pieceVB G E₂ ⊆ pieceZ G Z E₁ ∩ pieceZ G Z E₂ := by
  intro w hw
  rcases Finset.mem_inter.mp hw with ⟨hw₁, hw₂⟩
  rcases mem_edgeEnds.mp hw₁ with ⟨e₁, he₁, hinc₁⟩
  rcases mem_edgeEnds.mp hw₂ with ⟨e₂, he₂, hinc₂⟩
  have he₂_not_E₁ : e₂ ∉ E₁ := Finset.disjoint_right.mp hdisj he₂
  have he₁_not_E₂ : e₁ ∉ E₂ := Finset.disjoint_left.mp hdisj he₁
  have hw_VA₁ : w ∈ pieceVA G E₁ :=
    mem_edgeEnds.mpr ⟨e₂, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he₂_not_E₁⟩, hinc₂⟩
  have hw_VA₂ : w ∈ pieceVA G E₂ :=
    mem_edgeEnds.mpr ⟨e₁, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he₁_not_E₂⟩, hinc₁⟩
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hw_VA₁, hw₁⟩,
     Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hw_VA₂, hw₂⟩⟩

theorem pieceZ_union_subset {G : ComputeDigraph} (Z : Finset (Fin G.numVerts))
    (E₁ E₂ : Finset (Fin G.numEdges)) :
    pieceZ G Z (E₁ ∪ E₂) ⊆ pieceZ G Z E₁ ∪ pieceZ G Z E₂ := by
  intro w hw
  rcases Finset.mem_inter.mp hw with ⟨hw_AZ, hw_VB⟩
  rw [pieceVB, edgeEnds_union] at hw_VB
  rcases Finset.mem_union.mp hw_VB with hw₁ | hw₂
  · apply Finset.mem_union_left
    refine Finset.mem_inter.mpr ⟨?_, hw₁⟩
    rcases Finset.mem_union.mp hw_AZ with hw_VA | hw_Z
    · apply Finset.mem_union_left
      exact edgeEnds_mono
        (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_left) hw_VA
    · exact Finset.mem_union_right _ hw_Z
  · apply Finset.mem_union_right
    refine Finset.mem_inter.mpr ⟨?_, hw₂⟩
    rcases Finset.mem_union.mp hw_AZ with hw_VA | hw_Z
    · apply Finset.mem_union_left
      exact edgeEnds_mono
        (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_right) hw_VA
    · exact Finset.mem_union_right _ hw_Z

/-- A certified `δ`-folio table for the subgraph `(pieceVB G E, E)` formed by an edge set `E ⊆ E(G)`
and its ends, relative to `pieceZ G Z E = (pieceVA G E ∪ Z) ∩ pieceVB G E`. -/
abbrev PieceFolioTable (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (δ : ℕ)
    (E : Finset (Fin G.numEdges)) : Type :=
  CertFolioTable G (pieceVB G E) E (finsetRootFn (pieceZ G Z E)) δ

/-- Base step for an edge piece `E ⊆ E(G)` (GM XIII (4.1) Step (1), page 76). -/
def baseEdgePieceTable (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (δ : ℕ)
    (E : Finset (Fin G.numEdges)) : PieceFolioTable G Z δ E :=
  baseCertFolioTable G (pieceVB G E) E (finsetRootFn (pieceZ G Z E)) δ

/-- Combination step for two disjoint edge pieces `E₁, E₂ ⊆ E(G)` (GM XIII (4.1) Steps (2)–(3),
page 76). -/
def combineEdgePieceTables {G : ComputeDigraph} {Z : Finset (Fin G.numVerts)} {δ : ℕ}
    {E₁ E₂ : Finset (Fin G.numEdges)} (hdisj : Disjoint E₁ E₂)
    (T₁ : PieceFolioTable G Z δ E₁)
    (T₂ : PieceFolioTable G Z δ E₂) :
    PieceFolioTable G Z δ (E₁ ∪ E₂) :=
  (combinePieceTables
    (pieceZ_subset_pieceVB G Z E₁)
    (pieceZ_subset_pieceVB G Z E₂)
    (pieceZ_union_subset Z E₁ E₂)
    hdisj
    (fun _ he => ⟨head_mem_edgeEnds he, tail_mem_edgeEnds he⟩)
    (fun _ he => ⟨head_mem_edgeEnds he, tail_mem_edgeEnds he⟩)
    (pieceVB_inter_subset_pieceZ Z hdisj)
    T₁ T₂).castSets (edgeEnds_union G E₁ E₂).symm rfl rfl

/-- The set of vertices of `G` that contribute to the order of an edge `f ∈ E(T)` in a
branch-decomposition `(T, τ)` of a digraph `G` (GM XIII, Section 3, page 70). -/
def digraphTreeEdgeCutVerts {t : ℕ} (G : ComputeDigraph)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin G.numEdges → Fin t) (f : Sym2 (Fin t)) : Finset (Fin G.numVerts) :=
  Finset.univ.filter (fun w : Fin G.numVerts =>
    ∃ e₁ : Fin G.numEdges, ∃ e₂ : Fin G.numEdges,
      digraphIncident G w e₁ ∧ digraphIncident G w e₂ ∧
      ¬ (T.deleteEdges {f}).Reachable (τ e₁) (τ e₂))

/-- The order of a tree edge `f ∈ E(T)` in `(T, τ)` for a digraph `G`. -/
def digraphTreeEdgeOrder {t : ℕ} (G : ComputeDigraph)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin G.numEdges → Fin t) (f : Sym2 (Fin t)) : ℕ :=
  (digraphTreeEdgeCutVerts G T τ f).card

/-- A branch-decomposition `(T, τ)` of a digraph `G : ComputeDigraph` of width `≤ ω`, as defined in
Graph Minors XIII, Section 3, page 70 and (4.1), page 75:
(i) `T` is a tree and every vertex of `T` has valency 1 or 3;
(ii) `τ` is a bijection from `E(G)` to the set of leaves of `T`;
and every edge `f ∈ E(T)` has order `≤ ω`. -/
def IsDigraphBranchDecompOfWidthLe {t : ℕ} (ω : ℕ) (G : ComputeDigraph)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (τ : Fin G.numEdges → Fin t) : Prop :=
  IsCubicOrLeafTree T ∧
  Set.BijOn τ Set.univ (treeLeaves T : Set (Fin t)) ∧
  ∀ f ∈ T.edgeFinset, digraphTreeEdgeOrder G T τ f ≤ ω

theorem inSubtree_le (p : ℕ → ℕ) :
    ∀ {x y : ℕ}, inSubtree p x y = true → x ≤ y := by
  intro x y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    cases y with
    | zero =>
      unfold inSubtree
      simp only [beq_iff_eq]
      intro h
      omega
    | succ y' =>
      unfold inSubtree
      split_ifs with h1 h2
      · intro _
        rw [beq_iff_eq] at h1
        omega
      · intro hsub
        have := ih (p (y' + 1)) h2 hsub
        omega
      · intro h
        cases h

theorem inSubtree_zero_eq_true {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) :
    ∀ {y : ℕ}, y < t → inSubtree p 0 y = true := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro hy_lt
    cases y with
    | zero => exact inSubtree_self p 0
    | succ y' =>
      have hy_pos : 0 < y' + 1 := Nat.succ_pos y'
      rw [inSubtree_step hp hy_pos hy_lt (Nat.succ_ne_zero y')]
      have hpy : p (y' + 1) < y' + 1 := hp (y' + 1) hy_pos hy_lt
      exact ih (p (y' + 1)) hpy (Nat.lt_trans hpy hy_lt)

theorem inSubtree_child_iff {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) {x : ℕ} (hx_lt : x < t) :
    ∀ {y : ℕ}, y < t →
      (inSubtree p x y = true ↔
        y = x ∨ ∃ c, x < c ∧ c < t ∧ p c = x ∧ inSubtree p c y = true) := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro hy_lt
    by_cases hyx : y = x
    · subst hyx
      simp [inSubtree_self]
    · by_cases hy0 : y = 0
      · subst hy0
        have hx_pos : 0 < x := by omega
        rw [inSubtree_zero_of_pos p hx_pos]
        simp only [Bool.false_eq_true, hyx, false_or, false_iff, not_exists, not_and]
        intro c hc_gt _ _ hsub
        have := inSubtree_le p hsub
        omega
      · have hy_pos : 0 < y := by omega
        have hpy_lt : p y < y := hp y hy_pos hy_lt
        rw [inSubtree_step hp hy_pos hy_lt hyx]
        rw [ih (p y) hpy_lt (Nat.lt_trans hpy_lt hy_lt)]
        constructor
        · rintro (hpy_eq | ⟨c, hxc, hct, hpc, hsub⟩)
          · right
            refine ⟨y, ?_, hy_lt, hpy_eq, inSubtree_self p y⟩
            omega
          · right
            refine ⟨c, hxc, hct, hpc, ?_⟩
            have hyc : y ≠ c := by
              have hcle := inSubtree_le p hsub
              omega
            rwa [inSubtree_step hp hy_pos hy_lt hyc]
        · rintro (rfl | ⟨c, hxc, hct, hpc, hsub⟩)
          · exact False.elim (hyx rfl)
          · by_cases hyc : y = c
            · subst hyc
              exact Or.inl hpc
            · right
              refine ⟨c, hxc, hct, hpc, ?_⟩
              rwa [← inSubtree_step hp hy_pos hy_lt hyc]

theorem inSubtree_children_disjoint {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {x c₁ c₂ : ℕ} (hc₁_pos : 0 < c₁) (hc₂_pos : 0 < c₂)
    (hpc₁ : p c₁ = x) (hpc₂ : p c₂ = x) (hne : c₁ ≠ c₂) :
    ∀ {y : ℕ}, y < t → inSubtree p c₁ y = true → inSubtree p c₂ y = true → False := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro hy_lt h₁ h₂
    have hc₁_le : c₁ ≤ y := inSubtree_le p h₁
    have hc₂_le : c₂ ≤ y := inSubtree_le p h₂
    have hy_pos : 0 < y := by omega
    have hpy_lt : p y < y := hp y hy_pos hy_lt
    by_cases hy₁ : y = c₁
    · have hy₂ : y ≠ c₂ := hy₁ ▸ hne
      rw [inSubtree_step hp hy_pos hy_lt hy₂, hy₁, hpc₁] at h₂
      have hc₂_le_x : c₂ ≤ x := inSubtree_le p h₂
      have hpc₂_lt : p c₂ < c₂ := hp c₂ hc₂_pos (Nat.lt_of_le_of_lt hc₂_le hy_lt)
      omega
    · by_cases hy₂ : y = c₂
      · rw [inSubtree_step hp hy_pos hy_lt hy₁, hy₂, hpc₂] at h₁
        have hc₁_le_x : c₁ ≤ x := inSubtree_le p h₁
        have hpc₁_lt : p c₁ < c₁ := hp c₁ hc₁_pos (Nat.lt_of_le_of_lt hc₁_le hy_lt)
        omega
      · rw [inSubtree_step hp hy_pos hy_lt hy₁] at h₁
        rw [inSubtree_step hp hy_pos hy_lt hy₂] at h₂
        exact ih (p y) hpy_lt (Nat.lt_trans hpy_lt hy_lt) h₁ h₂

/-- Subtree edge set `E(B_x) = {e ∈ E(G) | inSubtree p x (τ e).1 = true}` at node `x` of
`parentTree t p` (GM XIII (4.1), page 75). -/
def dpEB (G : ComputeDigraph) {t : ℕ} (p : ℕ → ℕ) (τ : Fin G.numEdges → Fin t) (x : ℕ) :
    Finset (Fin G.numEdges) :=
  Finset.univ.filter (fun e => inSubtree p x (τ e).1 = true)

/-- Complementary edge set `E(A_x) = {e ∈ E(G) | inSubtree p x (τ e).1 = false}`. -/
def dpEA (G : ComputeDigraph) {t : ℕ} (p : ℕ → ℕ) (τ : Fin G.numEdges → Fin t) (x : ℕ) :
    Finset (Fin G.numEdges) :=
  Finset.univ.filter (fun e => inSubtree p x (τ e).1 = false)

theorem sdiff_dpEB (G : ComputeDigraph) {t : ℕ} (p : ℕ → ℕ) (τ : Fin G.numEdges → Fin t) (x : ℕ) :
    Finset.univ \ dpEB G p τ x = dpEA G p τ x := by
  ext e
  simp [dpEB, dpEA]

/-- For `x : Fin t` with `0 < x.1`, the boundary intersection `V(A_x) ∩ V(B_x)` equals
`digraphTreeEdgeCutVerts G (parentTree t p) τ s(⟨p x.1, _⟩, x)`, hence has size `≤ ω` in any
branch-decomposition of width `≤ ω` (GM XIII (4.1), page 75). -/
theorem pieceVA_inter_pieceVB_dpEB_eq {t : ℕ} (G : ComputeDigraph) (ht : 0 < t)
    {p : ℕ → ℕ} (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) {x : Fin t} (hx_pos : 0 < x.1) :
    pieceVA G (dpEB G p τ x.1) ∩ pieceVB G (dpEB G p τ x.1) =
      digraphTreeEdgeCutVerts G (parentTree t p) τ
        s(⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩, x) := by
  ext w
  simp only [Finset.mem_inter, pieceVA, pieceVB, mem_edgeEnds, dpEB, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true, digraphTreeEdgeCutVerts,
    parentTree_deleteEdge_reachable_iff ht hp hx_pos]
  constructor
  · rintro ⟨⟨e₁, he₁, hinc₁⟩, ⟨e₂, he₂, hinc₂⟩⟩
    exact ⟨e₁, e₂, hinc₁, hinc₂, by rw [he₁, he₂]; decide⟩
  · rintro ⟨e₁, e₂, hinc₁, hinc₂, hne⟩
    cases h₁ : inSubtree p x.1 (τ e₁).1 <;> cases h₂ : inSubtree p x.1 (τ e₂).1
    · exact False.elim (hne (by rw [h₁, h₂]))
    · exact ⟨⟨e₁, h₁, hinc₁⟩, ⟨e₂, h₂, hinc₂⟩⟩
    · exact ⟨⟨e₂, h₂, hinc₂⟩, ⟨e₁, h₁, hinc₁⟩⟩
    · exact False.elim (hne (by rw [h₁, h₂]))

theorem card_pieceZ_dpEB_le {t ω ξ : ℕ} {G : ComputeDigraph} {Z : Finset (Fin G.numVerts)}
    (hZ : Z.card ≤ ξ) (ht : 0 < t) {p : ℕ → ℕ} (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Fin G.numEdges → Fin t}
    (hbd : IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ)
    {x : Fin t} (hx_pos : 0 < x.1) :
    (pieceZ G Z (dpEB G p τ x.1)).card ≤ ω + ξ := by
  have hsub : pieceZ G Z (dpEB G p τ x.1) ⊆
      (pieceVA G (dpEB G p τ x.1) ∩ pieceVB G (dpEB G p τ x.1)) ∪ Z := by
    intro w hw
    rcases Finset.mem_inter.mp hw with ⟨hw_AZ, hw_B⟩
    rcases Finset.mem_union.mp hw_AZ with hw_A | hw_Z
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hw_A, hw_B⟩)
    · exact Finset.mem_union_right _ hw_Z
  have hcard1 : (pieceZ G Z (dpEB G p τ x.1)).card ≤
      (pieceVA G (dpEB G p τ x.1) ∩ pieceVB G (dpEB G p τ x.1)).card + Z.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [pieceVA_inter_pieceVB_dpEB_eq G ht hp τ hx_pos] at hcard1
  have hf_mem :
      s(⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩, x) ∈ (parentTree t p).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, parentTree_adj_of_lt hp]
    exact Or.inr ⟨hx_pos, rfl⟩
  have hord :
      digraphTreeEdgeOrder G (parentTree t p) τ
        s(⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩, x) ≤ ω :=
    hbd.2.2 _ hf_mem
  unfold digraphTreeEdgeOrder at hord
  omega

/-- Accumulated subtree edges at node `x` from `x` itself and children `c ∈ [x + 1, k)`. -/
def dpAccEB (G : ComputeDigraph) {t : ℕ} (p : ℕ → ℕ) (τ : Fin G.numEdges → Fin t)
    (x k : ℕ) : Finset (Fin G.numEdges) :=
  Finset.univ.filter (fun e =>
    (τ e).1 = x ∨
    ∃ c : Fin t, x < c.1 ∧ c.1 < k ∧ p c.1 = x ∧ inSubtree p c.1 (τ e).1 = true)

theorem dpAccEB_self (G : ComputeDigraph) {t : ℕ} (p : ℕ → ℕ) (τ : Fin G.numEdges → Fin t)
    (x : ℕ) :
    dpAccEB G p τ x (x + 1) = Finset.univ.filter (fun e => (τ e).1 = x) := by
  ext e
  simp only [dpAccEB, Finset.mem_filter, Finset.mem_univ, true_and]
  exact or_iff_left (by rintro ⟨c, hxc, hck, _⟩; omega)

theorem dpAccEB_step_ne (G : ComputeDigraph) {t : ℕ} (p : ℕ → ℕ) (τ : Fin G.numEdges → Fin t)
    {x k : ℕ} (hpk : p k ≠ x) :
    dpAccEB G p τ x (k + 1) = dpAccEB G p τ x k := by
  ext e
  simp only [dpAccEB, Finset.mem_filter, Finset.mem_univ, true_and]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨c, hxc, hck, hpc, hsub⟩
    have hck_ne : c.1 ≠ k := fun h => hpk (h ▸ hpc)
    exact ⟨c, hxc, by omega, hpc, hsub⟩
  · rintro ⟨c, hxc, hck, hpc, hsub⟩
    exact ⟨c, hxc, by omega, hpc, hsub⟩

theorem dpAccEB_step_eq (G : ComputeDigraph) {t : ℕ} (p : ℕ → ℕ) (τ : Fin G.numEdges → Fin t)
    {x k : ℕ} (hkt : k < t) (hxk : x < k) (hpk : p k = x) :
    dpAccEB G p τ x (k + 1) = dpAccEB G p τ x k ∪ dpEB G p τ k := by
  ext e
  simp only [dpAccEB, dpEB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hex | ⟨c, hxc, hck, hpc, hsub⟩)
    · exact Or.inl (Or.inl hex)
    · by_cases hck_eq : c.1 = k
      · rw [hck_eq] at hsub
        exact Or.inr hsub
      · exact Or.inl (Or.inr ⟨c, hxc, by omega, hpc, hsub⟩)
  · rintro ((hex | ⟨c, hxc, hck, hpc, hsub⟩) | hsub_k)
    · exact Or.inl hex
    · exact Or.inr ⟨c, hxc, by omega, hpc, hsub⟩
    · exact Or.inr ⟨⟨k, hkt⟩, hxk, Nat.lt_succ_self k, hpk, hsub_k⟩

theorem disjoint_dpAccEB_dpEB (G : ComputeDigraph) {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) {x k : ℕ} (hxk : x < k) (hpk : p k = x) :
    Disjoint (dpAccEB G p τ x k) (dpEB G p τ k) := by
  refine Finset.disjoint_left.mpr fun e he_acc he_k => ?_
  simp only [dpAccEB, Finset.mem_filter, Finset.mem_univ, true_and] at he_acc
  simp only [dpEB, Finset.mem_filter, Finset.mem_univ, true_and] at he_k
  have hkle : k ≤ (τ e).1 := inSubtree_le p he_k
  rcases he_acc with hex | ⟨c, hxc, hck, hpc, hsub_c⟩
  · omega
  · exact inSubtree_children_disjoint hp (by omega) (by omega) hpc hpk (by omega) (τ e).2
      hsub_c he_k

theorem dpAccEB_full (G : ComputeDigraph) {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) {x : ℕ} (hx_lt : x < t) :
    dpAccEB G p τ x t = dpEB G p τ x := by
  ext e
  simp only [dpAccEB, dpEB, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [inSubtree_child_iff hp hx_lt (τ e).2]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨c, hxc, hct, hpc, hsub⟩
    exact ⟨c.1, hxc, c.2, hpc, hsub⟩
  · rintro ⟨c, hxc, hct, hpc, hsub⟩
    exact ⟨⟨c, hct⟩, hxc, hct, hpc, hsub⟩

/-- Helper loop accumulating child tables `c ∈ [k, t)` with `p c = x` at node `x`. -/
def dpChildrenLoop (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (δ : ℕ)
    {t : ℕ} (p : ℕ → ℕ) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) (x : ℕ)
    (childFn : ∀ k, x < k → k < t → PieceFolioTable G Z δ (dpEB G p τ k))
    (k : ℕ) (hk_ge : x + 1 ≤ k) (hk_le : k ≤ t)
    (acc : PieceFolioTable G Z δ (dpAccEB G p τ x k)) :
    PieceFolioTable G Z δ (dpAccEB G p τ x t) :=
  if hkt : k < t then
    have hxk : x < k := by omega
    let nextAcc : PieceFolioTable G Z δ (dpAccEB G p τ x (k + 1)) :=
      if hpk : p k = x then
        have hdisj := disjoint_dpAccEB_dpEB G hp τ hxk hpk
        have childTable : PieceFolioTable G Z δ (dpEB G p τ k) :=
          childFn k hxk hkt
        (combineEdgePieceTables hdisj acc childTable).castSets
          (by rw [dpAccEB_step_eq G p τ hkt hxk hpk])
          (dpAccEB_step_eq G p τ hkt hxk hpk).symm
          (by rw [dpAccEB_step_eq G p τ hkt hxk hpk])
      else
        acc.castSets
          (by rw [dpAccEB_step_ne G p τ hpk])
          (dpAccEB_step_ne G p τ hpk).symm
          (by rw [dpAccEB_step_ne G p τ hpk])
    dpChildrenLoop G Z δ p hp τ x childFn (k + 1) (by omega) (by omega) nextAcc
  else
    have hkeq : k = t := by omega
    hkeq ▸ acc
termination_by t - k
decreasing_by omega

/-- Recursive computation of the certified `δ`-folio table for `dpEB G p τ x` on `parentTree t p`,
implementing Steps (1), (2), and (3) of GM XIII (4.1) (pages 75–76). -/
def dpSubtreeTable (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (δ : ℕ)
    {t : ℕ} (p : ℕ → ℕ) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) (x : ℕ) (hx_lt : x < t) :
    PieceFolioTable G Z δ (dpEB G p τ x) :=
  let initTable : PieceFolioTable G Z δ (dpAccEB G p τ x (x + 1)) :=
    (baseEdgePieceTable G Z δ (Finset.univ.filter (fun e => (τ e).1 = x))).castSets
      (by rw [dpAccEB_self]) (dpAccEB_self G p τ x).symm (by rw [dpAccEB_self])
  (dpChildrenLoop G Z δ p hp τ x
    (fun k _hxk hkt => dpSubtreeTable G Z δ p hp τ k hkt)
    (x + 1) (le_refl _) (by omega) initTable).castSets
    (by rw [dpAccEB_full G hp τ hx_lt])
    (dpAccEB_full G hp τ hx_lt)
    (by rw [dpAccEB_full G hp τ hx_lt])
termination_by t - x
decreasing_by omega

theorem dpEB_zero_eq_univ (G : ComputeDigraph) {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (τ : Fin G.numEdges → Fin t) :
    dpEB G p τ 0 = Finset.univ := by
  ext e
  simp [dpEB, inSubtree_zero_eq_true hp (τ e).2]

theorem pieceZ_univ_eq (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) :
    pieceZ G Z Finset.univ = Z ∩ pieceVB G Finset.univ := by
  simp [pieceZ, pieceVA]

/-- Prefix of vertices added during the isolated-vertex completion pass:
all non-isolated vertices `pieceVB G Finset.univ` together with vertices `< k`. -/
def dpVertPrefix (G : ComputeDigraph) (k : ℕ) : Finset (Fin G.numVerts) :=
  pieceVB G Finset.univ ∪ Finset.univ.filter (fun v : Fin G.numVerts => v.1 < k)

theorem dpVertPrefix_zero (G : ComputeDigraph) :
    dpVertPrefix G 0 = pieceVB G Finset.univ := by
  ext v
  simp [dpVertPrefix]

theorem dpVertPrefix_full (G : ComputeDigraph) :
    dpVertPrefix G G.numVerts = Finset.univ := by
  ext v
  simp [dpVertPrefix]

theorem dpVertPrefix_step_mem (G : ComputeDigraph) {v : Fin G.numVerts}
    (hv : v ∈ dpVertPrefix G v.1) :
    dpVertPrefix G (v.1 + 1) = dpVertPrefix G v.1 := by
  ext u
  simp only [dpVertPrefix, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  constructor
  · rintro (huB | hult)
    · exact Or.inl huB
    · by_cases huv : u.1 = v.1
      · have hueq : u = v := Fin.ext huv
        subst hueq
        exact hv
      · exact Or.inr (by omega)
  · rintro (huB | hult)
    · exact Or.inl huB
    · exact Or.inr (by omega)

theorem dpVertPrefix_step_not_mem (G : ComputeDigraph) (v : Fin G.numVerts) :
    dpVertPrefix G (v.1 + 1) = dpVertPrefix G v.1 ∪ {v} := by
  ext u
  simp only [dpVertPrefix, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Fin.ext_iff]
  by_cases hu : u ∈ pieceVB G Finset.univ <;> simp [hu]
  omega

/-- Extend a certified `δ`-folio table on `(pieceVB G Finset.univ, Finset.univ)` across all
isolated vertices of `G` (GM XIII (4.1), page 75: "Since the effect of isolated vertices of $G$ on the folio is clear, we may arrange (by deleting them) that $G$ has no isolated vertices"). -/
def addIsolatedVertsTable (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (δ : ℕ)
    (T₀ : CertFolioTable G (pieceVB G Finset.univ) Finset.univ
      (finsetRootFn (Z ∩ pieceVB G Finset.univ)) δ) :
    CertFolioTable G Finset.univ Finset.univ (finsetRootFn Z) δ :=
  let rec loop (k : ℕ) (hk : k ≤ G.numVerts)
      (acc : CertFolioTable G (dpVertPrefix G k) Finset.univ
        (finsetRootFn (Z ∩ dpVertPrefix G k)) δ) :
      CertFolioTable G (dpVertPrefix G G.numVerts) Finset.univ
        (finsetRootFn (Z ∩ dpVertPrefix G G.numVerts)) δ :=
    if hlt : k < G.numVerts then
      let v : Fin G.numVerts := ⟨k, hlt⟩
      let nextAcc : CertFolioTable G (dpVertPrefix G (k + 1)) Finset.univ
          (finsetRootFn (Z ∩ dpVertPrefix G (k + 1))) δ :=
        if hv : v ∈ dpVertPrefix G k then
          acc.castSets
            (dpVertPrefix_step_mem G hv).symm rfl
            (by rw [dpVertPrefix_step_mem G hv])
        else
          let singleT : CertFolioTable G {v} ∅ (finsetRootFn (Z ∩ {v})) δ :=
            baseCertFolioTable G {v} ∅ (finsetRootFn (Z ∩ {v})) δ
          have hVB_sub : ∀ e ∈ (Finset.univ : Finset (Fin G.numEdges)),
              G.head e ∈ dpVertPrefix G k ∧ G.tail e ∈ dpVertPrefix G k :=
            fun _ he =>
              ⟨Finset.mem_union_left _ (head_mem_edgeEnds he),
               Finset.mem_union_left _ (tail_mem_edgeEnds he)⟩
          have hinter : dpVertPrefix G k ∩ {v} ⊆ (Z ∩ dpVertPrefix G k) ∩ (Z ∩ {v}) := by
            intro u hu
            rcases Finset.mem_inter.mp hu with ⟨hu_pre, hu_v⟩
            rw [Finset.mem_singleton] at hu_v
            subst hu_v
            exact False.elim (hv hu_pre)
          have hZ_sub : Z ∩ (dpVertPrefix G k ∪ {v}) ⊆
              (Z ∩ dpVertPrefix G k) ∪ (Z ∩ {v}) := by
            intro u hu
            rw [Finset.inter_union_distrib_left] at hu
            exact hu
          (combinePieceTables
            Finset.inter_subset_right
            Finset.inter_subset_right
            hZ_sub
            (Finset.disjoint_empty_right _)
            hVB_sub
            (fun _ he => by simp at he)
            hinter
            acc singleT).castSets
            (dpVertPrefix_step_not_mem G v).symm
            (Finset.union_empty _)
            (by rw [dpVertPrefix_step_not_mem G v])
      loop (k + 1) (by omega) nextAcc
    else
      have hkeq : k = G.numVerts := by omega
      hkeq ▸ acc
  termination_by G.numVerts - k
  decreasing_by omega
  let initAcc : CertFolioTable G (dpVertPrefix G 0) Finset.univ
      (finsetRootFn (Z ∩ dpVertPrefix G 0)) δ :=
    T₀.castSets (dpVertPrefix_zero G).symm rfl (by rw [dpVertPrefix_zero])
  (loop 0 (Nat.zero_le _) initAcc).castSets
    (dpVertPrefix_full G) rfl (by rw [dpVertPrefix_full, Finset.inter_univ])

/-- **Complete dynamic programming algorithm of GM XIII (4.1) (pages 75–76):**
Given a digraph `G`, a root subset `Z ⊆ V(G)`, detail bound `δ`, and a parent-array
branch-decomposition `(t, p, τ)` of `G`, computes the certified `δ`-folio table of `G` relative to
`finsetRootFn Z` (containing one representative rooted digraph per isomorphism class in the
`δ`-folio together with its `PieceRootedModel` certificate). -/
def computeFolioDP (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (δ : ℕ)
    {t : ℕ} (ht : 0 < t) (p : ℕ → ℕ) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) :
    CertFolioTable G Finset.univ Finset.univ (finsetRootFn Z) δ :=
  let rootPiece : PieceFolioTable G Z δ Finset.univ :=
    (dpSubtreeTable G Z δ p hp τ 0 ht).castSets
      (by rw [dpEB_zero_eq_univ G hp τ])
      (dpEB_zero_eq_univ G hp τ)
      (by rw [dpEB_zero_eq_univ G hp τ])
  let edgesTable : CertFolioTable G (pieceVB G Finset.univ) Finset.univ
      (finsetRootFn (Z ∩ pieceVB G Finset.univ)) δ :=
    rootPiece.castSets rfl rfl (pieceZ_univ_eq G Z)
  addIsolatedVertsTable G Z δ edgesTable

/-- **Correctness of `computeFolioDP` (GM XIII (4.1), pages 75–76):**
1. The entries of `computeFolioDP` are pairwise non-isomorphic rooted digraphs of detail `≤ δ`.
2. Every entry `e ∈ (computeFolioDP G Z δ ht p hp τ).entries` carries a valid `RootedDigraphModel`
   `e.model.toRootedDigraphModel : RootedDigraphModel (withRoots G (finsetRootFn Z)) e.H`.
3. Every `Z.card`-rooted digraph `H` of detail `≤ δ` is isomorphic to some entry in
   `(computeFolioDP G Z δ ht p hp τ).entries` if and only if `H` belongs to the `δ`-folio of `G`
   relative to `finsetRootFn Z` (that is, `HasRootedDigraphModel (withRoots G (finsetRootFn Z)) H`).
   -/
theorem computeFolioDP_memIso_iff (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (δ : ℕ)
    {t : ℕ} (ht : 0 < t) (p : ℕ → ℕ) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t)
    {H : ComputeRootedDigraph Z.card} (hdet : H.HasDetailLe δ) :
    (computeFolioDP G Z δ ht p hp τ).toFolioSetRep.MemIso H ↔
      HasRootedDigraphModel H (withRoots G (finsetRootFn Z)) := by
  rw [CertFolioTable.memIso_toFolioSetRep_iff _ hdet]
  exact hasPieceRootedModel_univ_iff G (finsetRootFn Z) H

end GraphMinor.Compute
