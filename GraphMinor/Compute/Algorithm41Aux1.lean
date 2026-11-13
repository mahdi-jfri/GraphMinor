module

public import GraphMinor.Compute.Algorithm41Comb
public import GraphMinor.Compute.FolioStatement
public import GraphMinor.Compute.BitSet

/-!
# GM XIII Algorithm (4.1), Auxiliary 1: Pure Output Reader, Raw Entries, and Boundary Invariants

This file develops the first layer of infrastructure for the Word RAM implementation of
Algorithm (4.1) from Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
Section 4, pages 75–76:

1. **Pure-data output types (`Alg41DecodedEntry`, `Alg41DecodedOutput`) and pure stream readers
   (`decFolioCodesWords`, `decOneModelWords`, `decModelsWords`, `decAlg41OutWords`):**
   Reads `encFolioSetRep F` followed by the serialized models from `outArr : List ℕ` using only
   `List.getD`, `List.take`, `List.drop`, `decRootedDigraph`, and `finsetOfBitList` (no search,
   no dynamic program, no `Classical.choose`).
2. **Type-erased certified entries (`RawCertEntry`, `CertFolioTable.toRawList`):**
   Erases the piece indices `(VA, EA, Z)` from `CertFolioEntry` so that `CertFolioTable.castSets`
   is the identity (`toRawList_castSets`), and proves round-trip decoding of
   `encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList`.
3. **Constant-time boundary root maintenance (`subInc`, `capVal`) and tree-degree bounds:**
   Characterizes `v ∈ pieceZ G Z E` by `0 < subInc G E v ∧ subInc G E v < capVal G Z v`, proves the
   additive update of `subInc` across `pieceZ G Z E₁ ∪ pieceZ G Z E₂`, and bounds the number of
   children per node (`≤ 3`), leaf edges per node (`≤ 1`), and intermediate boundary size
   (`≤ max 2 (ω + ξ)`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: Pure-Data Output Types and Pure Stream Readers for (4.1) -/

/-- Default 1-vertex, 0-edge `q`-rooted digraph used only as a fallback value in `decOneModelWords`
when `decRootedDigraph` encounters ill-formed bytes. -/
def defaultRootedDigraph (q : ℕ) : ComputeRootedDigraph q where
  digraph :=
    { numVerts := 1
      numEdges := 0
      head := Fin.elim0
      tail := Fin.elim0 }
  roots := fun _ => ⟨0, Nat.one_pos⟩

/-- Pure-data entry read from `outArr` for a member `H` of the `δ`-folio of `G` relative to `Z`
together with its written-out model in `G`:
- `code`: the flat word-list folio code of `H` read from the `encFolioSetRep` section of `outArr`,
- `H`: the `q`-rooted digraph read from the model section of `outArr`,
- `edgeIdx`: for each edge `d` of `H`, the edge index in `G` representing `d`,
- `vertVerts`: for each vertex `u` of `H`, the vertex set `V(G_u) ⊆ V(G)` read from its bit-list,
- `vertEdges`: for each vertex `u` of `H`, the edge set `E(G_u) ⊆ E(G)` read from its bit-list. -/
structure Alg41DecodedEntry (G : ComputeDigraph) (q : ℕ) where
  /-- Flat word-list code of `H` read from the `encFolioSetRep` section. -/
  code : List ℕ
  /-- Decoded `q`-rooted digraph `H`. -/
  H : ComputeRootedDigraph q
  /-- For each edge `d` of `H`, the index of the representing edge in `G`. -/
  edgeIdx : Fin H.digraph.numEdges → ℕ
  /-- For each vertex `u` of `H`, the vertex subset `V(G_u) ⊆ V(G)`. -/
  vertVerts : Fin H.digraph.numVerts → Finset (Fin G.numVerts)
  /-- For each vertex `u` of `H`, the edge subset `E(G_u) ⊆ E(G)`. -/
  vertEdges : Fin H.digraph.numVerts → Finset (Fin G.numEdges)

/-- Pure-data output of Algorithm (4.1) read from `outArr : List ℕ`:
- `folioCodes`: the list of folio codes read from the `encFolioSetRep` prefix of `outArr`,
- `entries`: the list of folio entries with their written-out models read from `outArr`. -/
structure Alg41DecodedOutput (G : ComputeDigraph) (q : ℕ) where
  /-- List of folio codes read from the `encFolioSetRep` prefix of `outArr`. -/
  folioCodes : List (List ℕ)
  /-- List of decoded entries `(code, H, edgeIdx, vertVerts, vertEdges)`. -/
  entries : List (Alg41DecodedEntry G q)

/-- Pure stream reader that reads one length-prefixed word list `c.length :: c` from the front of
`words : List ℕ` and returns `(c, remainingWords)`. -/
def decOneLenPrefixedWords (words : List ℕ) : List ℕ × List ℕ :=
  let len := words.getD 0 0
  ((words.drop 1).take len, words.drop (1 + len))

theorem decOneLenPrefixedWords_append (c rest : List ℕ) :
    decOneLenPrefixedWords ((c.length :: c) ++ rest) = (c, rest) := by
  unfold decOneLenPrefixedWords
  simp only [List.cons_append, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero,
    List.take_left, Nat.add_comm 1 c.length, List.drop_left]

/-- Pure stream reader that reads `k` length-prefixed word lists from `words : List ℕ`. -/
def decLenPrefixedListWords : ℕ → List ℕ → List (List ℕ) × List ℕ
  | 0, words => ([], words)
  | k + 1, words =>
    let (c, rest₁) := decOneLenPrefixedWords words
    let (cs, rest₂) := decLenPrefixedListWords k rest₁
    (c :: cs, rest₂)

theorem decLenPrefixedListWords_append (cs : List (List ℕ)) (rest : List ℕ) :
    decLenPrefixedListWords cs.length (cs.flatMap (fun c => c.length :: c) ++ rest) =
      (cs, rest) := by
  induction cs generalizing rest with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
      decLenPrefixedListWords, decOneLenPrefixedWords_append, ih]

/-- Pure stream reader that reads `encFolioSetRep F` (`[codes.length] ++ codes.flatMap ...`) from
the front of `words : List ℕ` and returns `(codes, remainingWords)`. -/
def decFolioCodesWords (words : List ℕ) : List (List ℕ) × List ℕ :=
  decLenPrefixedListWords (words.getD 0 0) (words.drop 1)

theorem decFolioCodesWords_append {q δ : ℕ} (F : FolioSetRep q δ) (rest : List ℕ) :
    decFolioCodesWords (encFolioSetRep F ++ rest) = (F.codes, rest) := by
  unfold decFolioCodesWords encFolioSetRep
  simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.drop_succ_cons,
    List.drop_zero]
  exact decLenPrefixedListWords_append F.codes rest

/-- Pure stream reader that reads one model block (`edgeMap ++ vertBitLists`) for the member encoded
by `c : List ℕ` from `words : List ℕ` and returns `(entry, remainingWords)`. -/
def decOneModelWords (G : ComputeDigraph) (q : ℕ) (c : List ℕ) (words : List ℕ) :
    Alg41DecodedEntry G q × List ℕ :=
  let H := (decRootedDigraph q c).getD (defaultRootedDigraph q)
  let v_H := H.digraph.numVerts
  let m_H := H.digraph.numEdges
  let edgeWords := words.take m_H
  let rest₁ := words.drop m_H
  let n := G.numVerts
  let m := G.numEdges
  let rest₂ := rest₁.drop (v_H * (n + m))
  let entry : Alg41DecodedEntry G q :=
    { code := c
      H := H
      edgeIdx := fun d => edgeWords.getD d.1 0
      vertVerts := fun u => finsetOfBitList n ((rest₁.drop (u.1 * (n + m))).take n)
      vertEdges := fun u => finsetOfBitList m ((rest₁.drop (u.1 * (n + m) + n)).take m) }
  (entry, rest₂)

/-- Pure stream reader that reads a list of model blocks paired with `codes : List (List ℕ)`. -/
def decModelsWords (G : ComputeDigraph) (q : ℕ) :
    List (List ℕ) → List ℕ → List (Alg41DecodedEntry G q) × List ℕ
  | [], words => ([], words)
  | c :: cs, words =>
    let (e, rest₁) := decOneModelWords G q c words
    let (es, rest₂) := decModelsWords G q cs rest₁
    (e :: es, rest₂)

/-- Pure reader from `out : List ℕ` into `Alg41DecodedOutput G q`:
reads `folioCodes` from the `encFolioSetRep` prefix of `out`, then reads one model block per code in
`folioCodes`. -/
def decAlg41OutWords (G : ComputeDigraph) (q : ℕ) (out : List ℕ) : Alg41DecodedOutput G q :=
  let (codes, rest) := decFolioCodesWords out
  let (entries, _) := decModelsWords G q codes rest
  { folioCodes := codes, entries := entries }

/-! ### Section 2: Type-Erased Certified Entries (`RawCertEntry`) and Round-Trip Decoding -/

/-- Type-erased representation of a `CertFolioEntry G VA EA r δ`, holding only the root count `q`,
the rooted digraph `H : ComputeRootedDigraph q`, and the vertex/edge maps of its model in `G`.
Because `VA`, `EA`, and `r` do not appear in its type, `RawCertEntry G` is invariant under
`CertFolioTable.castSets`. -/
structure RawCertEntry (G : ComputeDigraph) (q : ℕ) where
  /-- Representative `q`-rooted digraph `H`. -/
  H : ComputeRootedDigraph q
  /-- For each vertex `u` of `H`, the vertex set `V(G_u) ⊆ V(G)`. -/
  vertVerts : Fin H.digraph.numVerts → Finset (Fin G.numVerts)
  /-- For each vertex `u` of `H`, the edge set `E(G_u) ⊆ E(G)`. -/
  vertEdges : Fin H.digraph.numVerts → Finset (Fin G.numEdges)
  /-- For each edge `d` of `H`, the representing edge in `G`. -/
  edgeMap : Fin H.digraph.numEdges → Fin G.numEdges

/-- Erase the piece and proof indices from a `CertFolioEntry`. -/
def CertFolioEntry.toRaw {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (e : CertFolioEntry G VA EA r δ) : RawCertEntry G q where
  H := e.H
  vertVerts := fun u => (e.model.vertMap u).verts
  vertEdges := fun u => (e.model.vertMap u).edges
  edgeMap := e.model.edgeMap

/-- Convert a `CertFolioTable` to its list of `RawCertEntry G q`s. -/
def CertFolioTable.toRawList {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (T : CertFolioTable G VA EA r δ) : List (RawCertEntry G q) :=
  T.entries.map CertFolioEntry.toRaw

/-- Flat word-list encoding of a single `RawCertEntry G q` model block:
`edgeMap ++ vertBitLists`. -/
def encRawCertEntry {G : ComputeDigraph} {q : ℕ} (e : RawCertEntry G q) : List ℕ :=
  (List.finRange e.H.digraph.numEdges).map (fun d => (e.edgeMap d).1) ++
    (List.finRange e.H.digraph.numVerts).flatMap (fun u =>
      bitSetList (e.vertVerts u) ++ bitSetList (e.vertEdges u))

/-- Flat word-list encoding of all model blocks in `es : List (RawCertEntry G q)`. -/
def encRawCertModels {G : ComputeDigraph} {q : ℕ} (es : List (RawCertEntry G q)) : List ℕ :=
  es.flatMap encRawCertEntry

/-- Convert a `RawCertEntry G q` into the decoded `Alg41DecodedEntry G q`. -/
def RawCertEntry.toAlg41DecodedEntry {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) : Alg41DecodedEntry G q where
  code := encRootedDigraph e.H
  H := e.H
  edgeIdx := fun d => (e.edgeMap d).1
  vertVerts := e.vertVerts
  vertEdges := e.vertEdges

private theorem flatMap_finRange_drop_take {α : Type*} (k L : ℕ) (f : Fin k → List α)
    (hlen : ∀ i : Fin k, (f i).length = L) (i : Fin k) :
    (((List.finRange k).flatMap f).drop (i.1 * L)).take L = f i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, Nat.zero_mul, List.drop_zero]
      exact List.take_left' (hlen 0)
    · simp only [Fin.val_succ]
      have hadd : (j.1 + 1) * L = (f 0).length + j.1 * L := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, hlen 0]
      rw [hadd, ← List.drop_drop, List.drop_left]
      exact ih (fun j' => f j'.succ) (fun j' => hlen j'.succ) j

theorem decOneModelWords_encRawCertEntry {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (rest : List ℕ) :
    decOneModelWords G q (encRootedDigraph e.H) (encRawCertEntry e ++ rest) =
      (e.toAlg41DecodedEntry, rest) := by
  rcases e with ⟨H, vertVerts, vertEdges, edgeMap⟩
  let n := G.numVerts
  let m := G.numEdges
  let v_H := H.digraph.numVerts
  let m_H := H.digraph.numEdges
  let edgePart : List ℕ := (List.finRange m_H).map (fun d => (edgeMap d).1)
  let fVert : Fin v_H → List ℕ := fun u => bitSetList (vertVerts u) ++ bitSetList (vertEdges u)
  let vertPart : List ℕ := (List.finRange v_H).flatMap fVert
  have hedge_len : edgePart.length = m_H := by simp [edgePart]
  have hfVert_len : ∀ u : Fin v_H, (fVert u).length = n + m := by
    intro u; simp [fVert, n, m]
  have hvert_len : vertPart.length = v_H * (n + m) := by
    simp [vertPart, List.length_flatMap, fVert, n, m, List.sum_replicate]
  have hassoc : encRawCertEntry ⟨H, vertVerts, vertEdges, edgeMap⟩ ++ rest =
      edgePart ++ (vertPart ++ rest) := by
    simp [encRawCertEntry, edgePart, vertPart, fVert, v_H, m_H, List.append_assoc]
  rw [hassoc]
  let words := edgePart ++ (vertPart ++ rest)
  have htake_edge : words.take m_H = edgePart :=
    List.take_left' hedge_len
  have hdrop_edge : words.drop m_H = vertPart ++ rest :=
    List.drop_left' hedge_len
  have hdrop_vert : (vertPart ++ rest).drop (v_H * (n + m)) = rest :=
    List.drop_left' hvert_len
  have hH_dec :
      (decRootedDigraph q (encRootedDigraph H)).getD (defaultRootedDigraph q) = H := by
    rw [decRootedDigraph_encRootedDigraph]
    rfl
  unfold decOneModelWords RawCertEntry.toAlg41DecodedEntry
  dsimp only
  have hslice_u : ∀ u : Fin v_H,
      ((vertPart ++ rest).drop (u.1 * (n + m))).take (n + m) = fVert u := by
    intro u
    have hle : u.1 * (n + m) + (n + m) ≤ vertPart.length := by
      rw [hvert_len]
      have : (u.1 + 1) * (n + m) ≤ v_H * (n + m) := Nat.mul_le_mul_right _ u.2
      rw [Nat.add_mul, Nat.one_mul] at this
      exact this
    rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    exact flatMap_finRange_drop_take v_H (n + m) fVert hfVert_len u
  -- Generalize the decoded `ComputeRootedDigraph q` and substitute `hH_dec`
  revert hH_dec
  generalize (decRootedDigraph q (encRootedDigraph H)).getD (defaultRootedDigraph q) = H_dec
  intro hH_dec
  subst hH_dec
  rw [Prod.mk.injEq]
  refine ⟨?_, by change (words.drop m_H).drop (v_H * (n + m)) = rest; rw [hdrop_edge, hdrop_vert]⟩
  have hedge_eq :
      (fun d : Fin m_H => (words.take m_H).getD d.1 0) =
      (fun d : Fin m_H => (edgeMap d).1) := by
    funext d
    rw [htake_edge]
    have hd : d.1 < edgePart.length := by rw [hedge_len]; exact d.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd, Option.getD_some]
    simp [edgePart]
  have hvv_eq :
      (fun u : Fin v_H =>
        finsetOfBitList n (((words.drop m_H).drop (u.1 * (n + m))).take n)) =
      vertVerts := by
    funext u
    rw [hdrop_edge]
    have h1 : (((vertPart ++ rest).drop (u.1 * (n + m))).take (n + m)).take n =
        ((vertPart ++ rest).drop (u.1 * (n + m))).take n := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right n m)]
    rw [← h1, hslice_u u, List.take_left' (length_bitSetList (vertVerts u)),
        finsetOfBitList_bitSetList]
  have hve_eq :
      (fun u : Fin v_H =>
        finsetOfBitList m (((words.drop m_H).drop (u.1 * (n + m) + n)).take m)) =
      vertEdges := by
    funext u
    rw [hdrop_edge, ← List.drop_drop]
    have h2 : (((vertPart ++ rest).drop (u.1 * (n + m))).drop n).take m =
        (((vertPart ++ rest).drop (u.1 * (n + m))).take (n + m)).drop n := by
      rw [List.take_drop]
    rw [h2, hslice_u u, List.drop_left' (length_bitSetList (vertVerts u)),
        finsetOfBitList_bitSetList]
  rw [hedge_eq, hvv_eq, hve_eq]

theorem decModelsWords_encRawCertModels {G : ComputeDigraph} {q : ℕ}
    (es : List (RawCertEntry G q)) (rest : List ℕ) :
    decModelsWords G q (es.map (fun e => encRootedDigraph e.H)) (encRawCertModels es ++ rest) =
      (es.map RawCertEntry.toAlg41DecodedEntry, rest) := by
  induction es generalizing rest with
  | nil => rfl
  | cons e es ih =>
    rw [List.map_cons, encRawCertModels, List.flatMap_cons, List.append_assoc,
      decModelsWords, decOneModelWords_encRawCertEntry]
    dsimp only
    change (e.toAlg41DecodedEntry :: (decModelsWords G q (es.map (fun e => encRootedDigraph e.H))
        (encRawCertModels es ++ rest)).1,
      (decModelsWords G q (es.map (fun e => encRootedDigraph e.H))
        (encRawCertModels es ++ rest)).2) = _
    rw [ih]
    rfl

/-- Round-trip theorem for `decAlg41OutWords`: reading `encFolioSetRep T.toFolioSetRep ++
encRawCertModels T.toRawList` recovers `T.toFolioSetRep.codes` and the exact list of entries of
`T`. -/
theorem decAlg41OutWords_encode {q δ : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts}
    (T : CertFolioTable G VA EA r δ) (rest : List ℕ) :
    decAlg41OutWords G q (encFolioSetRep T.toFolioSetRep ++ (encRawCertModels T.toRawList ++ rest)) =
      { folioCodes := T.toFolioSetRep.codes
        entries := T.entries.map (fun e =>
          { code := encRootedDigraph e.H
            H := e.H
            edgeIdx := fun d => (e.model.edgeMap d).1
            vertVerts := fun u => (e.model.vertMap u).verts
            vertEdges := fun u => (e.model.vertMap u).edges }) } := by
  have hcodes : T.toFolioSetRep.codes = T.toRawList.map (fun e => encRootedDigraph e.H) := by
    simp [CertFolioTable.toFolioSetRep, CertFolioTable.toRawList, List.map_map,
      CertFolioEntry.toRaw]
  unfold decAlg41OutWords
  rw [decFolioCodesWords_append]
  dsimp only
  rw [hcodes, decModelsWords_encRawCertModels T.toRawList rest]
  dsimp only
  congr 1
  simp [CertFolioTable.toRawList, CertFolioEntry.toRaw, RawCertEntry.toAlg41DecodedEntry]

/-! ### Section 3: Incident Edge Counts (`subInc`, `capVal`) and `pieceZ` Characterization -/

/-- Set of edges of `G` incident with vertex `v : Fin G.numVerts`. -/
def incEdges (G : ComputeDigraph) (v : Fin G.numVerts) : Finset (Fin G.numEdges) :=
  Finset.univ.filter (fun e => digraphIncident G v e)

/-- Total number of edges of `G` incident with `v`. -/
def totalInc (G : ComputeDigraph) (v : Fin G.numVerts) : ℕ :=
  (incEdges G v).card

/-- Number of edges in `E ⊆ E(G)` incident with `v`. -/
def subInc (G : ComputeDigraph) (E : Finset (Fin G.numEdges)) (v : Fin G.numVerts) : ℕ :=
  (incEdges G v ∩ E).card

/-- Boundary capacity threshold for `v`: equal to `G.numEdges + 1` if `v ∈ Z` (so any positive
`subInc` is strictly below `capVal`), and `totalInc G v` if `v ∉ Z` (so `subInc < capVal` if and
only if `v` has an incident edge outside `E`). -/
def capVal (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (v : Fin G.numVerts) : ℕ :=
  if v ∈ Z then G.numEdges + 1 else totalInc G v

theorem subInc_le_totalInc (G : ComputeDigraph) (E : Finset (Fin G.numEdges))
    (v : Fin G.numVerts) :
    subInc G E v ≤ totalInc G v :=
  Finset.card_le_card Finset.inter_subset_left

theorem totalInc_le_numEdges (G : ComputeDigraph) (v : Fin G.numVerts) :
    totalInc G v ≤ G.numEdges := by
  calc totalInc G v ≤ (Finset.univ : Finset (Fin G.numEdges)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = G.numEdges := by simp

theorem mem_pieceVB_iff_subInc_pos (G : ComputeDigraph) (E : Finset (Fin G.numEdges))
    (v : Fin G.numVerts) :
    v ∈ pieceVB G E ↔ 0 < subInc G E v := by
  rw [pieceVB, mem_edgeEnds, subInc, Finset.card_pos, Finset.Nonempty]
  simp only [Finset.mem_inter, incEdges, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]

theorem mem_pieceVA_iff_subInc_lt_totalInc (G : ComputeDigraph) (E : Finset (Fin G.numEdges))
    (v : Fin G.numVerts) :
    v ∈ pieceVA G E ↔ subInc G E v < totalInc G v := by
  have hsdiff : incEdges G v \ (incEdges G v ∩ E) = incEdges G v ∩ (Finset.univ \ E) := by
    ext e
    simp [incEdges]
  have hcard_sdiff :
      (incEdges G v \ (incEdges G v ∩ E)).card = totalInc G v - subInc G E v :=
    Finset.card_sdiff_of_subset Finset.inter_subset_left
  have hle := subInc_le_totalInc G E v
  rw [pieceVA, mem_edgeEnds]
  have hne_iff :
      (∃ e ∈ Finset.univ \ E, digraphIncident G v e) ↔
        (incEdges G v \ (incEdges G v ∩ E)).Nonempty := by
    rw [hsdiff, Finset.Nonempty]
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, incEdges, Finset.mem_filter,
      true_and, and_comm]
  rw [hne_iff, ← Finset.card_pos, hcard_sdiff]
  omega

/-- Exact arithmetic characterization of `v ∈ pieceZ G Z E`:
`v ∈ pieceZ G Z E` if and only if `0 < subInc G E v` and `subInc G E v < capVal G Z v`. -/
theorem mem_pieceZ_iff_subInc_lt_capVal (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (E : Finset (Fin G.numEdges)) (v : Fin G.numVerts) :
    v ∈ pieceZ G Z E ↔ 0 < subInc G E v ∧ subInc G E v < capVal G Z v := by
  rw [pieceZ, Finset.mem_inter, Finset.mem_union,
      mem_pieceVA_iff_subInc_lt_totalInc, mem_pieceVB_iff_subInc_pos, and_comm]
  refine and_congr_right fun _ => ?_
  unfold capVal
  have hle1 := subInc_le_totalInc G E v
  have hle2 := totalInc_le_numEdges G v
  by_cases hvZ : v ∈ Z
  · simp [hvZ]; omega
  · simp [hvZ]

theorem subInc_union (G : ComputeDigraph) {E₁ E₂ : Finset (Fin G.numEdges)}
    (hdisj : Disjoint E₁ E₂) (v : Fin G.numVerts) :
    subInc G (E₁ ∪ E₂) v = subInc G E₁ v + subInc G E₂ v := by
  unfold subInc
  rw [Finset.inter_union_distrib_left]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_of_subset_right Finset.inter_subset_right
      (Finset.disjoint_of_subset_left Finset.inter_subset_right hdisj))

/-- If `Disjoint E₁ E₂`, `v ∈ pieceVB G E₂`, and `v ∉ pieceZ G Z E₁`, then `subInc G E₁ v = 0`. -/
theorem subInc_eq_zero_of_not_mem_pieceZ (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    {E₁ E₂ : Finset (Fin G.numEdges)} (hdisj : Disjoint E₁ E₂)
    {v : Fin G.numVerts} (hv_notZ1 : v ∉ pieceZ G Z E₁) (hv_VB2 : v ∈ pieceVB G E₂) :
    subInc G E₁ v = 0 := by
  by_contra hne
  have hpos1 : 0 < subInc G E₁ v := Nat.pos_of_ne_zero hne
  have hv_VB1 : v ∈ pieceVB G E₁ := (mem_pieceVB_iff_subInc_pos G E₁ v).mpr hpos1
  rcases mem_edgeEnds.mp hv_VB2 with ⟨e₂, he₂, hinc₂⟩
  have he₂_not1 : e₂ ∉ E₁ := Finset.disjoint_right.mp hdisj he₂
  have hv_VA1 : v ∈ pieceVA G E₁ :=
    mem_edgeEnds.mpr ⟨e₂, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he₂_not1⟩, hinc₂⟩
  exact hv_notZ1 (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hv_VA1, hv_VB1⟩)

/-- For any `v ∈ pieceZ G Z E₁ ∪ pieceZ G Z E₂` with `Disjoint E₁ E₂`, `subInc G (E₁ ∪ E₂) v` is
the sum of `(if v ∈ pieceZ G Z E₁ then subInc G E₁ v else 0)` and
`(if v ∈ pieceZ G Z E₂ then subInc G E₂ v else 0)`. -/
theorem subInc_union_of_mem_pieceZ_union (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    {E₁ E₂ : Finset (Fin G.numEdges)} (hdisj : Disjoint E₁ E₂)
    {v : Fin G.numVerts} (hv : v ∈ pieceZ G Z E₁ ∪ pieceZ G Z E₂) :
    subInc G (E₁ ∪ E₂) v =
      (if v ∈ pieceZ G Z E₁ then subInc G E₁ v else 0) +
      (if v ∈ pieceZ G Z E₂ then subInc G E₂ v else 0) := by
  rw [subInc_union G hdisj v]
  rcases Finset.mem_union.mp hv with hv1 | hv2
  · have hv_VB1 : v ∈ pieceVB G E₁ := pieceZ_subset_pieceVB G Z E₁ hv1
    by_cases hv2' : v ∈ pieceZ G Z E₂
    · simp [hv1, hv2']
    · have h0 : subInc G E₂ v = 0 :=
        subInc_eq_zero_of_not_mem_pieceZ G Z hdisj.symm hv2' hv_VB1
      simp [hv1, hv2', h0]
  · have hv_VB2 : v ∈ pieceVB G E₂ := pieceZ_subset_pieceVB G Z E₂ hv2
    by_cases hv1' : v ∈ pieceZ G Z E₁
    · simp [hv1', hv2]
    · have h0 : subInc G E₁ v = 0 :=
        subInc_eq_zero_of_not_mem_pieceZ G Z hdisj hv1' hv_VB2
      simp [hv1', hv2, h0]

/-! ### Section 4: Tree Children Bound (`≤ 3`), Leaf Edge Bound (`≤ 1`), and Intermediate `pieceZ` Bound -/

/-- Set of children of node `x` in `parentTree t p`: vertices `c : Fin t` with `x < c.1` and
`p c.1 = x`. -/
def childrenFinset (t : ℕ) (p : ℕ → ℕ) (x : ℕ) : Finset (Fin t) :=
  Finset.univ.filter (fun c : Fin t => x < c.1 ∧ p c.1 = x)

theorem childrenFinset_subset_neighborFinset {t : ℕ} (p : ℕ → ℕ)
    (hp : ∀ z, 0 < z → z < t → p z < z) (x : Fin t) :
    childrenFinset t p x.1 ⊆ (parentTree t p).neighborFinset x := by
  intro c hc
  simp only [childrenFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rw [SimpleGraph.mem_neighborFinset, parentTree_adj_of_lt hp]
  exact Or.inr ⟨by omega, hc.2.symm⟩

/-- In any branch-decomposition `(parentTree t p, τ)` of width `≤ ω`, every node `x : Fin t` has
at most 3 children (`(childrenFinset t p x.1).card ≤ 3`). -/
theorem card_childrenFinset_le_three {t ω : ℕ} {G : ComputeDigraph}
    {p : ℕ → ℕ} (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Fin G.numEdges → Fin t}
    (hbd : IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ)
    (x : Fin t) :
    (childrenFinset t p x.1).card ≤ 3 := by
  have hsub := Finset.card_le_card (childrenFinset_subset_neighborFinset p hp x)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hsub
  rcases hbd.1.2 x with hdeg1 | hdeg3 <;> omega

/-- In any branch-decomposition `(parentTree t p, τ)` of width `≤ ω`, at most 1 edge `e` of `G` has
`(τ e).1 = x`. -/
theorem card_leafEdges_le_one {t ω : ℕ} {G : ComputeDigraph}
    {p : ℕ → ℕ} {τ : Fin G.numEdges → Fin t}
    (hbd : IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ)
    (x : ℕ) :
    (Finset.univ.filter (fun e : Fin G.numEdges => (τ e).1 = x)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
  have hτ_eq : τ e₁ = τ e₂ := Fin.ext (he₁.trans he₂.symm)
  exact hbd.2.1.injOn (Set.mem_univ e₁) (Set.mem_univ e₂) hτ_eq

/-- For any single-edge or empty edge set `E` with `E.card ≤ 1`, `(pieceVB G E).card ≤ 2` and
`(pieceZ G Z E).card ≤ 2`. -/
theorem card_pieceZ_le_two_of_card_le_one (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    {E : Finset (Fin G.numEdges)} (hE : E.card ≤ 1) :
    (pieceVB G E).card ≤ 2 ∧ (pieceZ G Z E).card ≤ 2 := by
  have hVB : (pieceVB G E).card ≤ 2 := by
    rcases E.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
    · simp [pieceVB, edgeEnds]
    · have hsub : pieceVB G E ⊆ {G.head e₀, G.tail e₀} := by
        intro v hv
        rcases mem_edgeEnds.mp hv with ⟨e, he, hinc⟩
        have he_eq : e = e₀ := Finset.card_le_one.mp hE e he e₀ he₀
        subst he_eq
        rcases hinc with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
  exact ⟨hVB, (Finset.card_le_card (pieceZ_subset_pieceVB G Z E)).trans hVB⟩

end GraphMinor.Compute
