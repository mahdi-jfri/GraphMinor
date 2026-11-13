module

public import GraphMinor.Crossing.PlanarEulerFaces
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.HP25.EdgeFaces
import GraphMinor.HP25.SplitTools
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Euler's planar edge bounds and nonplanarity of `K₃,₃` (Sections 1 and 7.2 of the note)

This file proves Euler's planar edge bounds and the nonplanarity of `K₃,₃` as used in Sections 1
and 7.2 of `docs/crossing/crossing_extractor.tex`:

* `planar_edge_bound`: a simple planar graph on `N ≥ 3` vertices has at most `3N - 6` edges
  (Section 1; Section 7.2 uses it: "Its $3N-5$ kept edges of $K$ make it nonplanar by Euler's
  bound").
* `planar_bipartite_edge_bound`: a simple bipartite planar graph on `N ≥ 3` vertices has at most
  `2N - 4` edges.
* `not_planar_K33_sets` and `not_planar_completeBipartiteGraph_three`: `K₃,₃` is not planar
  ("In particular, $K_{3,3}$ is nonplanar: a bipartite planar graph on six vertices has at most
  eight edges, whereas $K_{3,3}$ has nine", Section 1).

When `G` has a cycle on `R`, every face `f ∈ φ.faces` has its frontier bounded by the subgraph
`φ.faceGraph f` of edges of `G` on `R` whose lines lie in `frontier f`; since `φ` has at least two
faces, `φ.faceGraph f` also has at least two faces, so it contains a cycle on `R` of length at
least `3` (or `4` when `G` is bipartite on `R`). Since each edge bounds at most `2` faces, double
counting gives `3 * φ.faces.ncard ≤ 2 * (edgesOn G R).ncard` (and `4 * φ.faces.ncard ≤
2 * (edgesOn G R).ncard` in the bipartite case), which combines with `φ.euler_ineq` to yield the
edge bounds.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set GraphMinor.HP25 GraphMinor.Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-! ### Bipartite graphs on a vertex set and cycle lengths -/

/-- `G` is bipartite on `R` if there is a 2-colouring of `V` that properly colours every edge of `G`
with both ends in `R`. -/
@[expose] def IsBipartiteOn (G : SimpleGraph V) (R : Set V) : Prop :=
  ∃ col : V → Bool, ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → col u ≠ col v

theorem IsBipartiteOn.mono {H : SimpleGraph V} {R' : Set V} (h : IsBipartiteOn G R)
    (hGH : ∀ u ∈ R', ∀ v ∈ R', H.Adj u v → G.Adj u v) (hR : R' ⊆ R) :
    IsBipartiteOn H R' := by
  obtain ⟨col, hcol⟩ := h
  exact ⟨col, fun u hu v hv huv => hcol u (hR hu) v (hR hv) (hGH u hu v hv huv)⟩

/-- A cycle `C` of `G` on a finite set `R` contributes at least `C.length` distinct edges to
`edgesOn G R`. -/
theorem isCycleList_length_le_edgesOn (hR : R.Finite) {C : List V} (hC : IsCycleList G C)
    (hCR : ∀ x ∈ C, x ∈ R) : C.length ≤ (edgesOn G R).ncard := by
  rcases C with _ | ⟨x, t⟩
  · simp [IsCycleList] at hC
  have hne : x :: t ≠ [] := List.cons_ne_nil x t
  let L := x :: t ++ [x]
  have hLlen : L.length = (x :: t).length + 1 := by simp [L]
  let g : Fin (x :: t).length → Sym2 V := fun i =>
    s(L[i.1]'(by omega), L[i.1 + 1]'(by omega))
  have hinj : Function.Injective g := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ he
    ext
    simp only
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact False.elim (PlaneEmbedding.closed_edge_ne hC.2.1 hC.1 hne hij hj he)
    · rfl
    · exact False.elim (PlaneEmbedding.closed_edge_ne hC.2.1 hC.1 hne hij hi he.symm)
  have hrange : range g ⊆ edgesOn G R := by
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    have hp : (L[i]'(by omega), L[i + 1]'(by omega)) ∈ (x :: t).zip ((x :: t).rotate 1) := by
      rw [zip_rotate_one_cons, mem_zip_tail_iff]
      exact ⟨i, by simp at hi ⊢; omega, rfl, rfl⟩
    have h1 := List.of_mem_zip hp
    exact mem_edgesOn_iff.mpr ⟨hCR _ h1.1, hCR _ (List.mem_rotate.mp h1.2), hC.2.2 _ hp⟩
  have hcard : (range g).ncard = (x :: t).length := by
    rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← hcard]
  exact ncard_le_ncard hrange (finite_edgesOn hR)

/-- In a graph bipartite on `R`, every cycle on `R` has length at least `4`. -/
theorem isCycleList_four_le_length_of_isBipartiteOn (hbip : IsBipartiteOn G R) {C : List V}
    (hC : IsCycleList G C) (hCR : ∀ x ∈ C, x ∈ R) : 4 ≤ C.length := by
  have h3 := hC.1
  by_contra hlt
  have hlen : C.length = 3 := by omega
  rcases C with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> try (simp at hlen)
  obtain ⟨col, hcol⟩ := hbip
  have hab : G.Adj a b := hC.2.2 (a, b) (by simp [List.rotate])
  have hbc : G.Adj b c := hC.2.2 (b, c) (by simp [List.rotate])
  have hca : G.Adj c a := hC.2.2 (c, a) (by simp [List.rotate])
  have h1 : col a ≠ col b := hcol a (hCR a (by simp)) b (hCR b (by simp)) hab
  have h2 : col b ≠ col c := hcol b (hCR b (by simp)) c (hCR c (by simp)) hbc
  have h3' : col c ≠ col a := hcol c (hCR c (by simp)) a (hCR a (by simp)) hca
  rcases ha : col a <;> rcases hb : col b <;> rcases hc : col c <;> simp_all

/-! ### Face-edge double counting -/

/-- Double counting on a finite bipartite relation `r : α → β → Prop`. -/
private theorem bipartite_ncard_mul_le {α β : Type*} {F : Set α} {E : Set β} (r : α → β → Prop)
    (hF : F.Finite) (hE : E.Finite) (k m : ℕ)
    (hleft : ∀ f ∈ F, k ≤ {e ∈ E | r f e}.ncard)
    (hright : ∀ e ∈ E, {f ∈ F | r f e}.ncard ≤ m) :
    k * F.ncard ≤ m * E.ncard := by
  classical
  let sF := hF.toFinset
  let sE := hE.toFinset
  have hFcard : F.ncard = sF.card := ncard_eq_toFinset_card F hF
  have hEcard : E.ncard = sE.card := ncard_eq_toFinset_card E hE
  have hL : ∀ f ∈ sF, k ≤ ∑ e ∈ sE, (if r f e then 1 else 0) := by
    intro f hf
    rw [← Finset.card_filter]
    have hfF : f ∈ F := hF.mem_toFinset.mp hf
    have hfin_sub : {e ∈ E | r f e}.Finite := hE.subset (fun _ h => h.1)
    have heq : hfin_sub.toFinset = sE.filter (r f) := by
      ext e
      simp [sE, hfin_sub.mem_toFinset, hE.mem_toFinset]
    rw [← heq, ← ncard_eq_toFinset_card _ hfin_sub]
    exact hleft f hfF
  have hR : ∀ e ∈ sE, (∑ f ∈ sF, (if r f e then 1 else 0)) ≤ m := by
    intro e he
    rw [← Finset.card_filter]
    have heE : e ∈ E := hE.mem_toFinset.mp he
    have hfin_sub : {f ∈ F | r f e}.Finite := hF.subset (fun _ h => h.1)
    have heq : hfin_sub.toFinset = sF.filter (fun f => r f e) := by
      ext f
      simp [sF, hfin_sub.mem_toFinset, hF.mem_toFinset]
    rw [← heq, ← ncard_eq_toFinset_card _ hfin_sub]
    exact hright e heE
  rw [hFcard, hEcard]
  calc
    k * sF.card = ∑ _f ∈ sF, k := by simp [Nat.mul_comm]
    _ ≤ ∑ f ∈ sF, ∑ e ∈ sE, (if r f e then 1 else 0) := Finset.sum_le_sum hL
    _ = ∑ e ∈ sE, ∑ f ∈ sF, (if r f e then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ _e ∈ sE, m := Finset.sum_le_sum hR
    _ = m * sE.card := by simp [Nat.mul_comm]

end GraphMinor.Crossing

namespace GraphMinor.HP25.PlaneEmbedding

open SimpleGraph Set GraphMinor.Surface GraphMinor.Crossing

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-- The subgraph of `G` on `R` consisting of edges whose drawn line lies in `frontier f`. -/
@[expose] def faceGraph (φ : PlaneEmbedding G R) (f : Set ℂ) : SimpleGraph V where
  Adj u v := u ∈ R ∧ v ∈ R ∧ G.Adj u v ∧ φ.line u v ⊆ frontier f
  symm := ⟨fun u v h => ⟨h.2.1, h.1, h.2.2.1.symm, φ.line_comm v u ▸ h.2.2.2⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.2.2.1⟩

/-- Whether an edge `e` has its drawn line inside `frontier f`. -/
@[expose] def IsFaceEdge (φ : PlaneEmbedding G R) (f : Set ℂ) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => φ.line u v ⊆ frontier f,
    fun u v => by simp [φ.line_comm u v]⟩ e

theorem edgesOn_faceGraph_eq (φ : PlaneEmbedding G R) (f : Set ℂ) :
    edgesOn (φ.faceGraph f) R = {e ∈ edgesOn G R | φ.IsFaceEdge f e} := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_edgesOn_iff, faceGraph, mem_ofPred_eq, IsFaceEdge, Sym2.lift_mk]
    tauto

/-- When `G` has a cycle on `R`, the boundary subgraph `φ.faceGraph f` of every face `f ∈ φ.faces`
contains a cycle on `R`. -/
theorem exists_cycle_faceGraph (φ : PlaneEmbedding G R) {C₀ : List V}
    (hC₀ : IsCycleList G C₀) (hC₀R : ∀ x ∈ C₀, x ∈ R) {f : Set ℂ} (hf : f ∈ φ.faces) :
    ∃ C, IsCycleList (φ.faceGraph f) C ∧ ∀ x ∈ C, x ∈ R := by
  by_contra hacyc
  let ψ : PlaneEmbedding (φ.faceGraph f) R := φ.mono (fun _ _ _ _ h => h.2.2.1) Subset.rfl
  have hψU : ψ.U ⊆ φ.U := by
    rintro z (⟨x, hx, rfl⟩ | hz)
    · exact φ.pt_mem_U hx
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ha, b, hb, hab, hz⟩ := hz
      exact φ.line_subset_U ha hb hab.2.2.1 hz
  obtain ⟨hfo, hfc, hfU⟩ := φ.isOpen_of_mem_faces hf
  have hfrψ : frontier f ⊆ ψ.U := by
    intro z hz
    have hzU : z ∈ φ.U := by
      by_contra hnot
      obtain ⟨g, hzg⟩ := φ.mem_faces_of_notMem hnot
      obtain ⟨w, hwg, hwf⟩ := mem_closure_iff.mp hz.1 _ (φ.isOpen_of_mem_faces g).1 hzg
      have heq := φ.eq_of_mem_faces hf g hwf hwg
      rw [← heq] at hzg
      rw [frontier, hfo.interior_eq] at hz
      exact hz.2 hzg
    by_cases hzpt : z ∈ φ.pt '' R
    · exact Or.inl hzpt
    · rcases hzU with h | hzL
      · exact absurd h hzpt
      · simp only [mem_iUnion] at hzL
        obtain ⟨u, hu, v, hv, huv, hzuv⟩ := hzL
        have hzu : z ≠ φ.pt u := fun h => hzpt ⟨u, hu, h.symm⟩
        have hzv : z ≠ φ.pt v := fun h => hzpt ⟨v, hv, h.symm⟩
        obtain ⟨f₁, _, f₂, _, hfr₁, hfr₂, honly, -⟩ := φ.edge_faces hu hv huv
        have hsub : φ.line u v ⊆ frontier f := by
          rcases honly f hf z hzuv hzu hzv hz.1 with rfl | rfl
          · exact hfr₁
          · exact hfr₂
        exact ψ.line_subset_U hu hv ⟨hu, hv, huv, hsub⟩ hzuv
  have hfψ : f ∈ ψ.faces :=
    ψ.mem_faces_of_frontier hfo hfc (hfU.trans (compl_subset_compl.mpr hψU)) hfrψ
  -- Find a second face of `φ` using the cycle `C₀`
  rcases C₀ with _ | ⟨u₀, _ | ⟨v₀, t₀⟩⟩
  · simp [IsCycleList] at hC₀
  · simp [IsCycleList] at hC₀
  have hp₀ : (u₀, v₀) ∈ (u₀ :: v₀ :: t₀).zip ((u₀ :: v₀ :: t₀).rotate 1) := by
    rw [zip_rotate_one_cons]; exact List.mem_cons_self
  have hu₀ : u₀ ∈ R := hC₀R u₀ (by simp)
  have hv₀ : v₀ ∈ R := hC₀R v₀ (by simp)
  have huv₀ : G.Adj u₀ v₀ := hC₀.2.2 (u₀, v₀) hp₀
  obtain ⟨f₁, hf₁, f₂, hf₂, -, -, -, hsep⟩ := φ.edge_faces hu₀ hv₀ huv₀
  have hne12 : f₁ ≠ f₂ := hsep (φ.cycleImage (u₀ :: v₀ :: t₀))
    (isJordanParts (φ.isOArc_cycleImage hC₀ hC₀R).some)
    (φ.cycleImage_subset_U hC₀ hC₀R)
    ((φ.line_subset_cycleImage_iff hC₀ hC₀R hu₀ hv₀ huv₀).mpr ⟨(u₀, v₀), hp₀, rfl⟩)
  have hex_other : ∃ g ∈ φ.faces, g ≠ f := by
    by_cases h1 : f₁ = f
    · exact ⟨f₂, hf₂, fun h2 => hne12 (h1.trans h2.symm)⟩
    · exact ⟨f₁, hf₁, h1⟩
  obtain ⟨g, hg, hgf⟩ := hex_other
  obtain ⟨_, hgc, hgU⟩ := φ.isOpen_of_mem_faces hg
  obtain ⟨b, hb⟩ := hgc.nonempty
  have hbU : b ∉ ψ.U := fun h => hgU hb (hψU h)
  obtain ⟨hgψ, hbgψ⟩ := ψ.mem_faces_of_notMem hbU
  have hsub := (ψ.faces_ncard_of_acyclic hacyc).1
  have heq : connectedComponentIn (univ \ ψ.U) b = f := hsub hgψ hfψ
  rw [heq] at hbgψ
  exact hgf (φ.eq_of_mem_faces hg hf hb hbgψ)

/-- Each edge `e ∈ edgesOn G R` lies on the frontier of at most two faces of `φ`. -/
theorem ncard_faces_isFaceEdge_le_two (φ : PlaneEmbedding G R) {e : Sym2 V} (he : e ∈ edgesOn G R) :
    {f ∈ φ.faces | φ.IsFaceEdge f e}.ncard ≤ 2 := by
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hu, hv, huv⟩ := mem_edgesOn_iff.mp he
    obtain ⟨f₁, _, f₂, _, _, _, honly, -⟩ := φ.edge_faces hu hv huv
    obtain ⟨p, hp, hpu, hpv⟩ := exists_inner_point (φ.isLine u hu v hv huv)
    have hsub : {f ∈ φ.faces | φ.IsFaceEdge f s(u, v)} ⊆ {f₁, f₂} := by
      rintro f ⟨hf, hfe⟩
      exact honly f hf p hp hpu hpv (hfe hp).1
    exact (ncard_le_ncard hsub (toFinite {f₁, f₂})).trans
      ((ncard_insert_le f₁ {f₂}).trans (by simp))

/-- When `G` has a cycle on `R`, `3 * φ.faces.ncard ≤ 2 * (edgesOn G R).ncard`. -/
theorem three_mul_faces_le_two_mul_edgesOn (φ : PlaneEmbedding G R) {C₀ : List V}
    (hC₀ : IsCycleList G C₀) (hC₀R : ∀ x ∈ C₀, x ∈ R) :
    3 * φ.faces.ncard ≤ 2 * (edgesOn G R).ncard := by
  refine bipartite_ncard_mul_le φ.IsFaceEdge (φ.faces_finite _ rfl) (finite_edgesOn φ.finite) 3 2
    (fun f hf => ?_) (fun e he => φ.ncard_faces_isFaceEdge_le_two he)
  obtain ⟨C, hC, hCR⟩ := φ.exists_cycle_faceGraph hC₀ hC₀R hf
  rw [← φ.edgesOn_faceGraph_eq f]
  exact hC.1.trans (isCycleList_length_le_edgesOn φ.finite hC hCR)

/-- When `G` is bipartite on `R` and has a cycle on `R`,
`4 * φ.faces.ncard ≤ 2 * (edgesOn G R).ncard`. -/
theorem four_mul_faces_le_two_mul_edgesOn (φ : PlaneEmbedding G R) (hbip : IsBipartiteOn G R)
    {C₀ : List V} (hC₀ : IsCycleList G C₀) (hC₀R : ∀ x ∈ C₀, x ∈ R) :
    4 * φ.faces.ncard ≤ 2 * (edgesOn G R).ncard := by
  refine bipartite_ncard_mul_le φ.IsFaceEdge (φ.faces_finite _ rfl) (finite_edgesOn φ.finite) 4 2
    (fun f hf => ?_) (fun e he => φ.ncard_faces_isFaceEdge_le_two he)
  obtain ⟨C, hC, hCR⟩ := φ.exists_cycle_faceGraph hC₀ hC₀R hf
  have hbip_f : IsBipartiteOn (φ.faceGraph f) R :=
    hbip.mono (fun _ _ _ _ h => h.2.2.1) Subset.rfl
  rw [← φ.edgesOn_faceGraph_eq f]
  exact (isCycleList_four_le_length_of_isBipartiteOn hbip_f hC hCR).trans
    (isCycleList_length_le_edgesOn φ.finite hC hCR)

/-- **Euler's planar edge bound** for a plane embedding `φ : PlaneEmbedding G R` with
`3 ≤ R.ncard`: `(edgesOn G R).ncard ≤ 3 * R.ncard - 6`. -/
theorem edgesOn_ncard_le (φ : PlaneEmbedding G R) (h3 : 3 ≤ R.ncard) :
    (edgesOn G R).ncard ≤ 3 * R.ncard - 6 := by
  have hRne : R.Nonempty := (ncard_pos φ.finite).mp (by omega)
  by_cases hcyc : ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R
  · obtain ⟨C, hC, hCR⟩ := hcyc
    have heuler := φ.euler_ineq _ hRne rfl
    have hfaces := φ.three_mul_faces_le_two_mul_edgesOn hC hCR
    omega
  · have hacyc := acyclic_edgesOn_bound (G := G) R.ncard φ.finite rfl hRne hcyc
    omega

/-- **Euler's bipartite planar edge bound** for a plane embedding `φ : PlaneEmbedding G R` with
`IsBipartiteOn G R` and `3 ≤ R.ncard`: `(edgesOn G R).ncard ≤ 2 * R.ncard - 4`. -/
theorem bipartite_edgesOn_ncard_le (φ : PlaneEmbedding G R) (hbip : IsBipartiteOn G R)
    (h3 : 3 ≤ R.ncard) :
    (edgesOn G R).ncard ≤ 2 * R.ncard - 4 := by
  have hRne : R.Nonempty := (ncard_pos φ.finite).mp (by omega)
  by_cases hcyc : ∃ C, IsCycleList G C ∧ ∀ x ∈ C, x ∈ R
  · obtain ⟨C, hC, hCR⟩ := hcyc
    have heuler := φ.euler_ineq _ hRne rfl
    have hfaces := φ.four_mul_faces_le_two_mul_edgesOn hbip hC hCR
    omega
  · have hacyc := acyclic_edgesOn_bound (G := G) R.ncard φ.finite rfl hRne hcyc
    omega

end GraphMinor.HP25.PlaneEmbedding

namespace GraphMinor.Crossing

open SimpleGraph Set GraphMinor.HP25 GraphMinor.Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-! ### Top-level Euler planar edge bounds -/

/-- **Euler's planar edge bound** (`docs/crossing/crossing_extractor.tex`, Sections 1 and 7.2:
"a planar graph with $N\ge3$ vertices has at most $3N-6$ edges", and "Its $3N-5$ kept edges of $K$
make it nonplanar by Euler's bound"):
a simple graph `G` planar on a vertex set `R` of size `R.ncard ≥ 3` has at most `3 * R.ncard - 6`
edges on `R`. -/
theorem planar_edge_bound (hP : Nonempty (PlaneEmbedding G R)) (h3 : 3 ≤ R.ncard) :
    (edgesOn G R).ncard ≤ 3 * R.ncard - 6 :=
  let ⟨φ⟩ := hP
  φ.edgesOn_ncard_le h3

/-- **Euler's planar edge bound** on `Set.univ` for a finite simple graph `G`. -/
theorem planar_edge_bound_univ [Fintype V] [DecidableRel G.Adj]
    (hP : Nonempty (PlaneEmbedding G univ)) (h3 : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨φ⟩ := hP
  have hR : (univ : Set V).ncard = Fintype.card V := by
    rw [ncard_univ, Nat.card_eq_fintype_card]
  have hE : (edgesOn G univ).ncard = G.edgeFinset.card := by
    have heq : edgesOn G univ = (G.edgeFinset : Set (Sym2 V)) := by
      ext e
      simp [edgesOn]
    rw [heq, ncard_coe_finset]
  have h := φ.edgesOn_ncard_le (hR ▸ h3)
  omega

/-- **Euler's bipartite planar edge bound** (`docs/crossing/crossing_extractor.tex`, Section 1:
"a bipartite planar graph with $N\ge3$ vertices has at most $2N-4$ edges"):
a simple graph `G` bipartite and planar on a vertex set `R` of size `R.ncard ≥ 3` has at most
`2 * R.ncard - 4` edges on `R`. -/
theorem planar_bipartite_edge_bound (hP : Nonempty (PlaneEmbedding G R))
    (hbip : IsBipartiteOn G R) (h3 : 3 ≤ R.ncard) :
    (edgesOn G R).ncard ≤ 2 * R.ncard - 4 :=
  let ⟨φ⟩ := hP
  φ.bipartite_edgesOn_ncard_le hbip h3

/-- **Euler's bipartite planar edge bound** on `Set.univ` for a finite bipartite simple graph `G`. -/
theorem planar_bipartite_edge_bound_univ [Fintype V] [DecidableRel G.Adj]
    (hP : Nonempty (PlaneEmbedding G univ)) (hbip : IsBipartiteOn G univ)
    (h3 : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 2 * Fintype.card V - 4 := by
  obtain ⟨φ⟩ := hP
  have hR : (univ : Set V).ncard = Fintype.card V := by
    rw [ncard_univ, Nat.card_eq_fintype_card]
  have hE : (edgesOn G univ).ncard = G.edgeFinset.card := by
    have heq : edgesOn G univ = (G.edgeFinset : Set (Sym2 V)) := by
      ext e
      simp [edgesOn]
    rw [heq, ncard_coe_finset]
  have h := φ.bipartite_edgesOn_ncard_le hbip (hR ▸ h3)
  omega

/-! ### `K₃,₃` is not planar -/

/-- **`K₃,₃` is not planar** (`docs/crossing/crossing_extractor.tex`, Section 1:
"In particular, $K_{3,3}$ is nonplanar: a bipartite planar graph on six vertices has at most eight
edges, whereas $K_{3,3}$ has nine"):
if `R` contains three distinct vertices `a 0, a 1, a 2` and three distinct vertices `b 0, b 1, b 2`
with `G.Adj (a i) (b j)` for all `i, j : Fin 3`, then `G` has no plane embedding on `R`. -/
theorem not_planar_K33_sets {a b : Fin 3 → V} (haR : ∀ i, a i ∈ R) (hbR : ∀ j, b j ∈ R)
    (hainj : Function.Injective a) (hbinj : Function.Injective b)
    (hadj : ∀ i j, G.Adj (a i) (b j)) :
    ¬ Nonempty (PlaneEmbedding G R) := by
  rintro ⟨φ⟩
  classical
  have hab_ne : ∀ i j, a i ≠ b j := fun i j h => G.ne_of_adj (hadj i j) h
  let S₀ : Set V := range a ∪ range b
  have hS₀R : S₀ ⊆ R := union_subset (range_subset_iff.mpr haR) (range_subset_iff.mpr hbR)
  have hdisj : Disjoint (range a) (range b) :=
    disjoint_left.mpr (by rintro _ ⟨i, rfl⟩ ⟨j, hj⟩; exact hab_ne i j hj.symm)
  have hcardS₀ : S₀.ncard = 6 := by
    rw [ncard_union_eq hdisj (toFinite _) (toFinite _),
      ncard_range_of_injective hainj, ncard_range_of_injective hbinj,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let H : SimpleGraph V := {
    Adj u v := (u ∈ range a ∧ v ∈ range b ∧ G.Adj u v) ∨ (u ∈ range b ∧ v ∈ range a ∧ G.Adj u v)
    symm := ⟨fun u v h => h.elim (fun ⟨h1, h2, h3⟩ => Or.inr ⟨h2, h1, h3.symm⟩)
      (fun ⟨h1, h2, h3⟩ => Or.inl ⟨h2, h1, h3.symm⟩)⟩
    loopless := ⟨fun u h => h.elim (fun ⟨_, _, h3⟩ => G.loopless.irrefl u h3)
      (fun ⟨_, _, h3⟩ => G.loopless.irrefl u h3)⟩
  }
  let ψ : PlaneEmbedding H S₀ := φ.mono
    (fun _ _ _ _ h => h.elim (fun h' => h'.2.2) (fun h' => h'.2.2)) hS₀R
  have hbip : IsBipartiteOn H S₀ := by
    refine ⟨fun u => decide (u ∈ range a), fun u _ v _ huv => ?_⟩
    rcases huv with ⟨huA, hvB, -⟩ | ⟨huB, hvA, -⟩
    · have hvnotA : v ∉ range a := disjoint_left.mp hdisj.symm hvB
      simp [huA, hvnotA]
    · have hunotA : u ∉ range a := disjoint_left.mp hdisj.symm huB
      simp [hunotA, hvA]
  have hbound : (edgesOn H S₀).ncard ≤ 8 := by
    have h := ψ.bipartite_edgesOn_ncard_le hbip (by omega)
    omega
  let eMap : Fin 3 × Fin 3 → Sym2 V := fun p => s(a p.1, b p.2)
  have heInj : Function.Injective eMap := by
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ he
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (hainj h1) (hbinj h2)
    · exact False.elim (hab_ne i₁ j₂ h1)
  have heSub : range eMap ⊆ edgesOn H S₀ := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact mem_edgesOn_iff.mpr ⟨Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩,
      Or.inl ⟨⟨i, rfl⟩, ⟨j, rfl⟩, hadj i j⟩⟩
  have h9 : 9 ≤ (edgesOn H S₀).ncard := by
    have hcard9 : (range eMap).ncard = 9 := by
      rw [ncard_range_of_injective heInj, Nat.card_eq_fintype_card,
        Fintype.card_prod, Fintype.card_fin]
    rw [← hcard9]
    exact ncard_le_ncard heSub (finite_edgesOn ψ.finite)
  omega

/-- **`K₃,₃` is not planar**: `completeBipartiteGraph (Fin 3) (Fin 3)` has no plane embedding on
`Set.univ`. -/
theorem not_planar_completeBipartiteGraph_three :
    ¬ Nonempty (PlaneEmbedding (completeBipartiteGraph (Fin 3) (Fin 3)) univ) :=
  not_planar_K33_sets (a := Sum.inl) (b := Sum.inr)
    (fun _ => trivial) (fun _ => trivial) Sum.inl_injective Sum.inr_injective
    (fun _ _ => Or.inl ⟨rfl, rfl⟩)

end GraphMinor.Crossing
