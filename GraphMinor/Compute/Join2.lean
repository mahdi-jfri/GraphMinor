module

public import GraphMinor.Compute.Algorithm33Multigraph
public import GraphMinor.Compute.Algorithm41Verified

/-!
# Joining the programs of Algorithms (3.3) and (4.1) with the interfaces of `Specs4.lean`

This file copies the subroutine specifications `Alg33Spec` and `Alg41Spec` of `Specs4.lean`,
together with their supporting definitions `FolioSetRep.decodedAt`, `encRootedDigraphModel`, and
`encFolioModels`, and proves how the programs of Algorithms (3.3) and (4.1) meet them:

1. **GM XIII Algorithm (3.3) (`Alg33Spec`):**
   `alg33MultiProg` in `GraphMinor/Compute/Algorithm33Multigraph.lean` meets `Alg33Spec` directly
   for every fixed `ω ≥ 2` and non-aliasing array indices (`alg33MultiProg_meets_alg33Spec`).
2. **GM XIII Algorithm (4.1) (`IsDeltaFolioRep` and `Alg41Spec`):**
   - `alg41Prog` and `decAlg41Out` in `GraphMinor/Compute/Algorithm41.lean` compute in `O(ε)` time
     on the Word RAM (via `ComputesArrRelInTime`) a certified output `out : Alg41Output x`
     satisfying `IsValidAlg41Output δ x out`.
   - From `hvalid : IsValidAlg41Output δ x out`, `hvalid.toFolioSetRep` is a
     `FolioSetRep x.Z.card δ` satisfying `IsDeltaFolioRep δ G Z` (from
     `GraphMinor/Compute/FolioStatement.lean`), and `hvalid.toFolioModels` extracts for every index
     `i : Fin hvalid.toFolioSetRep.codes.length` a concrete model
     `RootedDigraphModel (hvalid.toFolioSetRep.decodedAt i) (withRoots x.G (finsetRootFn x.Z))`
     (`algorithm_4_1_folio_and_models`).
   - Note on `Alg41Spec`: `Alg41Spec` asks for three things beyond the paper's statement of (4.1)
     (page 75) and the `ComputesArrRelInTime` convention of `Basic.lean`:
     (a) it takes `Z : List (Fin n)` without `Z.Nodup`, whereas the paper's (4.1) takes a subset
         $Z \subseteq V(G)$ with $|Z| \le \xi$ (and its proof on pages 75–76 operates on subsets
         $Z_1, Z_2 \subseteq V(G)$ at every tree edge);
     (b) it takes `IsValidBranchDecompCode ω_bd G bdCode`, which allows `G.numEdges ≤ 1` with
         `t = 0` (no tree $T$ at all), whereas the paper's (4.1) takes a branch-decomposition
         $(T, \tau)$ of $G$ where $T$ is a non-empty tree;
     (c) it requires `encFolioSetRep F` and `encFolioModels F models` in raw state arrays at the end
         of `Exec` without an output decoder (`decAlg41Out`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Supporting Definitions from `Specs4.lean` -/

/-- Convert `(G, Z)` (`G : MultiDigraph n`, `Z : List (Fin n)`) to a `ComputeRootedDigraph Z.length`. -/
abbrev MultiDigraph.toComputeRootedDigraph {n : ℕ} (G : MultiDigraph n) (Z : List (Fin n)) :
    ComputeRootedDigraph Z.length where
  digraph := G.toComputeDigraph
  roots := fun i => Z[i.1]'i.2

/-- Decode the `i`-th representative rooted digraph from a `FolioSetRep q δ`. -/
def FolioSetRep.decodedAt {q δ : ℕ} (F : FolioSetRep q δ) (i : Fin F.codes.length) :
    ComputeRootedDigraph q :=
  have hc : IsDetailLeCode q δ (F.codes[i.1]'i.2) := F.all_detail _ (List.getElem_mem _)
  match h : decRootedDigraph q (F.codes[i.1]'i.2) with
  | some H => H
  | none => False.elim (by unfold IsDetailLeCode at hc; rw [h] at hc; exact hc)

/-- Flat `List ℕ` encoding of a `RootedDigraphModel H G`:
`[H.digraph.numVerts, H.digraph.numEdges]` followed by the mapped edge endpoints `(tail, head)` for
`e : Fin H.digraph.numEdges` and, for each vertex `u : Fin H.digraph.numVerts`, the indicator
bitlist `bitSetList (M.vertMap u).verts` of length `G.digraph.numVerts`. -/
def encRootedDigraphModel {q : ℕ} {H G : ComputeRootedDigraph q}
    (M : RootedDigraphModel H G) : List ℕ :=
  [H.digraph.numVerts, H.digraph.numEdges] ++
  (List.finRange H.digraph.numEdges).flatMap (fun e =>
    [(G.digraph.tail (M.edgeMap e)).1, (G.digraph.head (M.edgeMap e)).1]) ++
  (List.finRange H.digraph.numVerts).flatMap (fun u =>
    bitSetList (M.vertMap u).verts)

theorem length_encRootedDigraphModel {q : ℕ} {H G : ComputeRootedDigraph q}
    (M : RootedDigraphModel H G) :
    (encRootedDigraphModel M).length =
      2 + 2 * H.digraph.numEdges + H.digraph.numVerts * G.digraph.numVerts := by
  unfold encRootedDigraphModel
  have h1 :
      ((List.finRange H.digraph.numEdges).flatMap (fun e =>
        [(G.digraph.tail (M.edgeMap e)).1,
         (G.digraph.head (M.edgeMap e)).1])).length =
      2 * H.digraph.numEdges := by
    rw [List.length_flatMap]
    simp [List.map_const', List.sum_replicate, List.length_finRange, Nat.mul_comm]
  have h2 :
      ((List.finRange H.digraph.numVerts).flatMap (fun u =>
        bitSetList (M.vertMap u).verts)).length = H.digraph.numVerts * G.digraph.numVerts := by
    rw [List.length_flatMap]
    have hmap :
        List.map (fun u => (bitSetList (M.vertMap u).verts).length)
          (List.finRange H.digraph.numVerts) =
        List.replicate (List.finRange H.digraph.numVerts).length G.digraph.numVerts := by
      rw [List.map_eq_replicate_iff]
      intro u _
      exact length_bitSetList (M.vertMap u).verts
    rw [hmap, List.length_finRange, List.sum_replicate, smul_eq_mul]
  simp only [List.length_append, List.length_cons, List.length_nil, h1, h2]

/-- Flat `List ℕ` encoding of a family of models ("a modelling of it") for each entry of a
`FolioSetRep q δ`:
`[F.codes.length]` followed by `mEnc.length :: mEnc` for each `i : Fin F.codes.length`. -/
def encFolioModels {q δ : ℕ} {G : ComputeRootedDigraph q}
    (F : FolioSetRep q δ)
    (models : ∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) G) : List ℕ :=
  [F.codes.length] ++
  (List.finRange F.codes.length).flatMap (fun i =>
    let mEnc := encRootedDigraphModel (models i)
    mEnc.length :: mEnc)

/-! ### Section 2: Subroutine Specifications `Alg33Spec` and `Alg41Spec` (from `Specs4.lean`) -/

/-- **Specification of GM XIII Algorithm (3.3) (page 72)** on a graph in the multigraph format:
> **(3.3) Algorithm.**
> *Input:* A graph $G$ with $|E(G)| \ge 2$.
> *Output:* A subgraph $G'$ of $G$ and a branch-decomposition of $G'$ of width $\le 3\omega$, such
> that either $G' = G$ or $G'$ has branch-width $\ge \omega$.
> *Running time:* $O(v^2 + \varepsilon)$. -/
def Alg33Spec (ω : ℕ) (a_in a_G_out a_bd_out a_base r_base : ℕ) (P33 : Cmd) : Prop :=
  open Classical in
  ∃ (C₃₃ c_w : ℕ), 0 < C₃₃ ∧ 0 < c_w ∧
    ∀ (n : ℕ) (G : MultiDigraph n) (w : ℕ),
      wordSize c_w ((n + 1) ^ 2 + G.numEdges) ≤ w →
      3 * ω < 2 ^ w →
      (∀ p ∈ G.activePairsList, G.edgeMult p.1 p.2 < 2 ^ w) →
      ∀ (s : State),
        s.arrs a_in = G.enc →
        ∃ (s' : State) (t : ℕ) (G' : MultiDigraph n) (bdCode : List ℕ),
          Exec w P33 s s' t ∧
          t ≤ C₃₃ * ((n + 1) ^ 2 + (G.numEdges + n + 1)) ∧
          G' ≤ G ∧
          IsValidBranchDecompCode (3 * ω) G' bdCode ∧
          (G' = G ∨ (G' ≠ G ∧ IsAlg33HighWidthCase ω G G')) ∧
          s'.arrs a_G_out = G'.enc ∧
          s'.arrs a_bd_out = bdCode ∧
          s'.regs r_base = (if G' = G then 1 else 0) ∧
          (∀ r < r_base, s'.regs r = s.regs r) ∧
          (∀ a < a_base, a ≠ a_G_out → a ≠ a_bd_out → s'.arrs a = s.arrs a)

/-- **Specification of GM XIII Algorithm (4.1) (page 75)** from `Specs4.lean`:
> **(4.1) Algorithm.**
> *Input:* A digraph $G$, and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$, and a
> branch-decomposition $(T, \tau)$ of $G$ of width $\le \omega$.
> *Output:* The $\delta$-folio of $G$ relative to $Z$, and a modelling of it.
> *Running time:* $O(\varepsilon)$. -/
def Alg41Spec (ξ δ ω_bd : ℕ)
    (a_G a_Z a_bd a_folio a_models a_base r_base : ℕ) (P41 : Cmd) : Prop :=
  ∃ (C₄₁ c_w : ℕ), 0 < C₄₁ ∧ 0 < c_w ∧
    ∀ (n : ℕ) (G : MultiDigraph n) (Z : List (Fin n)) (bdCode : List ℕ) (w : ℕ),
      Z.length ≤ ξ →
      IsValidBranchDecompCode ω_bd G bdCode →
      wordSize c_w (G.numEdges + n + 1) ≤ w →
      ω_bd < 2 ^ w →
      (∀ pair ∈ G.activePairsList, G.edgeMult pair.1 pair.2 < 2 ^ w) →
      ∀ (s : State),
        s.arrs a_G = G.enc →
        s.arrs a_Z = [Z.length] ++ Z.map Fin.val →
        s.arrs a_bd = bdCode →
        ∃ (s' : State) (t : ℕ) (F : FolioSetRep Z.length δ)
          (models : ∀ i : Fin F.codes.length,
            RootedDigraphModel (F.decodedAt i) (G.toComputeRootedDigraph Z)),
          Exec w P41 s s' t ∧
          t ≤ C₄₁ * (G.numEdges + n + 1) ∧
          (∀ H : ComputeRootedDigraph Z.length, H.HasDetailLe δ →
            (F.MemIso H ↔ HasRootedDigraphModel H (G.toComputeRootedDigraph Z))) ∧
          s'.arrs a_folio = encFolioSetRep F ∧
          s'.arrs a_models = encFolioModels F models ∧
          (∀ r < r_base, s'.regs r = s.regs r) ∧
          (∀ a < a_base, a ≠ a_folio → a ≠ a_models → s'.arrs a = s.arrs a)

/-! ### Section 3: Meeting `Alg33Spec` with `alg33MultiProg` -/

/-- `alg33MultiProg` meets `Alg33Spec` for every fixed `ω ≥ 2` and non-aliasing
array indices `< a_base`. -/
theorem alg33MultiProg_meets_alg33Spec (ω : ℕ) (hω : 2 ≤ ω)
    (a_in a_G_out a_bd_out a_base r_base : ℕ)
    (ha_in : a_in < a_base) (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (hne_in_G : a_in ≠ a_G_out) (hne_in_bd : a_in ≠ a_bd_out) (hne_G_bd : a_G_out ≠ a_bd_out) :
    Alg33Spec ω a_in a_G_out a_bd_out a_base r_base
      (alg33MultiProg ω a_in a_G_out a_bd_out a_base r_base) := by
  classical
  rcases algorithm_3_3_multigraph_cases ω hω a_in a_G_out a_bd_out a_base r_base
      ha_in ha_G ha_bd hne_in_G hne_in_bd hne_G_bd with
    ⟨C₃₃, c_w, hC, hcw, hexec⟩
  refine ⟨C₃₃, c_w, hC, hcw, fun n G w hw_size _ _ s hin => ?_⟩
  rcases hexec n G w hw_size s hin with
    ⟨s', t, G', bdCode, hex, ht, hle, hbd, hcases, hG_out, hbd_out, hr0, hreg, harr⟩
  have ht' : t ≤ C₃₃ * ((n + 1) ^ 2 + (G.numEdges + n + 1)) := by
    refine ht.trans (Nat.mul_le_mul_left C₃₃ ?_)
    omega
  exact ⟨s', t, G', bdCode, hex, ht', hle, hbd, hcases, hG_out, hbd_out, hr0, hreg, harr⟩

/-! ### Section 4: Extracting `FolioSetRep.decodedAt` Models from `Algorithm41` -/

theorem FolioSetRep.decodedAt_eq_of_eq_encRootedDigraph {q δ : ℕ}
    (F : FolioSetRep q δ) (i : Fin F.codes.length) (H : ComputeRootedDigraph q)
    (heq : F.codes[i.1]'i.2 = encRootedDigraph H) :
    F.decodedAt i = H := by
  unfold FolioSetRep.decodedAt
  split
  next H' h =>
    rw [heq, decRootedDigraph_encRootedDigraph] at h
    exact Option.some.inj h.symm
  next h =>
    rw [heq, decRootedDigraph_encRootedDigraph] at h
    nomatch h

theorem IsValidAlg41Output.decodedAt_toFolioSetRep_eq {δ ξ ω : ℕ}
    {x : Alg41Input ξ ω} {out : Alg41Output x}
    (hvalid : IsValidAlg41Output δ x out)
    (i : Fin hvalid.toFolioSetRep.codes.length) :
    hvalid.toFolioSetRep.decodedAt i =
      (out.entries[i.1]'(by
        have hlen : hvalid.toFolioSetRep.codes.length = out.entries.length := by
          simp [IsValidAlg41Output.toFolioSetRep]
        omega)).H := by
  have hi : i.1 < out.entries.length := by
    have hlen : hvalid.toFolioSetRep.codes.length = out.entries.length := by
      simp [IsValidAlg41Output.toFolioSetRep]
    omega
  let e := out.entries[i.1]'hi
  have he_mem : e ∈ out.entries := List.getElem_mem hi
  have hcode : e.code = encRootedDigraph e.H := (hvalid.1 e he_mem).1
  apply FolioSetRep.decodedAt_eq_of_eq_encRootedDigraph
  simp [IsValidAlg41Output.toFolioSetRep, e, hcode]

/-- Extract the family of concrete models
`∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) (withRoots x.G (finsetRootFn x.Z))`
from any valid output `out : Alg41Output x` of Algorithm (4.1). -/
def IsValidAlg41Output.toFolioModels {δ ξ ω : ℕ}
    {x : Alg41Input ξ ω} {out : Alg41Output x}
    (hvalid : IsValidAlg41Output δ x out)
    (i : Fin hvalid.toFolioSetRep.codes.length) :
    RootedDigraphModel (hvalid.toFolioSetRep.decodedAt i) (withRoots x.G (finsetRootFn x.Z)) :=
  have hi : i.1 < out.entries.length := by
    have hlen : hvalid.toFolioSetRep.codes.length = out.entries.length := by
      simp [IsValidAlg41Output.toFolioSetRep]
    omega
  hvalid.decodedAt_toFolioSetRep_eq i ▸ (out.entries[i.1]'hi).model

/-- Mathematical model certificates represented by the written data of a valid read output. -/
noncomputable def IsValidAlg41ReadOutput.toFolioModels {δ ξ ω : ℕ}
    {x : Alg41Input ξ ω} {out : Alg41DecodedOutput x.G x.Z.card}
    (hvalid : IsValidAlg41ReadOutput δ x out)
    (i : Fin hvalid.toFolioSetRep.codes.length) :
    RootedDigraphModel (hvalid.toFolioSetRep.decodedAt i) (withRoots x.G (finsetRootFn x.Z)) :=
  hvalid.certifiedValidity.toFolioModels i

/-- **Combined bridge theorem for GM XIII Algorithm (4.1):**
For every fixed `δ, ξ, ω : ℕ`, `alg41Prog δ ξ ω` runs in `O(ε)` time on the Word RAM, and for any
input `(G, Z, t, p, τ)` (`G : MultiDigraph n`, `Z : Finset (Fin n)` with `|Z| ≤ ξ`, and a
branch-decomposition `(parentTree t p, τ)` of `G` of width `≤ ω`), the decoded output
`decAlg41Out δ x out` yields both:
1. a `F : FolioSetRep Z.card δ` satisfying `IsDeltaFolioRep δ G Z` (from `FolioStatement.lean`), and
2. a family of concrete models
   `models : ∀ i : Fin F.codes.length, RootedDigraphModel (F.decodedAt i) (rootedDigraphOfZ G Z)`. -/
theorem algorithm_4_1_folio_and_models (δ ξ ω : ℕ) :
    ∃ (C c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ)
        {t : ℕ} (ht : 0 < t) {p : ℕ → ℕ} (hp : ∀ z, 0 < z → z < t → p z < z)
        {τ : Fin G.toComputeDigraph.numEdges → Fin t}
        (hbd : IsDigraphBranchDecompOfWidthLe ω G.toComputeDigraph (parentTree t p) τ)
        (s₀ : State),
        let x : Alg41Input ξ ω := ⟨G.toComputeDigraph, Z, hZ, t, ht, p, hp, τ, hbd⟩
        s₀.arrs inArr = encAlg41In x →
        ∃ (s' : State) (steps : ℕ)
          (F : FolioSetRep Z.card δ)
          (_models : ∀ i : Fin F.codes.length,
            RootedDigraphModel (F.decodedAt i) (rootedDigraphOfZ G Z)),
          Exec (wordSize c (alg41Size x)) (alg41Prog δ ξ ω) s₀ s' steps ∧
          steps ≤ C * alg41Size x ∧
          IsDeltaFolioRep δ G Z F ∧
          ∃ (hvalid : IsValidAlg41ReadOutput δ x (decAlg41Out δ x (s'.arrs outArr))),
            F = hvalid.toFolioSetRep := by
  rcases gm13_algorithm_4_1 δ ξ ω with ⟨C, c, hC, hc, hexec⟩
  refine ⟨C, c, hC, hc, fun {n} G Z hZ {t} ht {p} hp {τ} hbd s₀ hs₀ => ?_⟩
  let x : Alg41Input ξ ω := ⟨G.toComputeDigraph, Z, hZ, t, ht, p, hp, τ, hbd⟩
  rcases hexec x s₀ hs₀ with ⟨s', steps, hex, hsteps, hvalid⟩
  exact ⟨s', steps, hvalid.toFolioSetRep, hvalid.toFolioModels, hex,
    by simpa using hsteps,
    hvalid.isDeltaFolioRep G Z hZ ht hp hbd, hvalid, rfl⟩

end GraphMinor.Compute
