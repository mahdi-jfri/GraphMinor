module

public import GraphMinor.Compute.Algorithm64
public import GraphMinor.Compute.Algorithm62

/-!
# Graph Minors XIII, Algorithm (6.5) in the Word RAM Model

This file formalizes Algorithm (6.5) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110 (page 87):

> **Next, let $\xi, \delta \ge 0$ be integers.**
>
> **(6.5) Algorithm.**
> *Input:* A digraph $G$ and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
> *Output:* A subdigraph $G'$ of $G$ with $Z \subseteq V(G')$, such that $G$ and $G'$ have the same
> $\delta$-folio relative to $Z$, and such that $|E(G')| \le C|V(G')|$, where
> $C = \delta + 2(\delta+1)2^{p-3}$ and where $p = \lfloor\frac{5}{2}\xi\rfloor + 3\delta + 1$.
> *Running time:* $O(v^3)$.
>
> *Description:*
> (1) Let $H$ be a maximal subdigraph of $G$ with at most $\delta$ loops at each vertex and at most
>     $\delta+1$ edges with head $u$ and tail $v$, for all distinct $u, v \in V(G)$. Certainly $G$
>     and $H$ have the same $\delta$-folios relative to $Z$.
> (2) We set $G_1 = H$ and perform a recursion. At the start of the $i$th iteration we have a
>     subdigraph $G_i$ of $H$ with $Z \subseteq V(G_i)$ and $|V(G_i)| = |V(H)| - i + 1$ such that
>     $G_i$ and $H$ (and hence $G$) have the same $\delta$-folios relative to $Z$. If
>     $|E(G_i)| \le C|V(G_i)|$ we set $G' = G_i$ and stop. Otherwise, the $i$th iteration proceeds
>     as follows.
> (3) Let $J_i$ be the simple (undirected) graph underlying $G_i$. Then
>     $(\delta + 2(\delta+1)2^{p-3})|V(J_i)| = C|V(G_i)| \le |E(G_i)| \le \delta|V(J_i)| + 2(\delta+1)|E(J_i)|$
>     and so $2^{p-3}|V(J_i)| \le |E(J_i)|$. We apply (6.4) to $J_i$ and obtain a model of $K_p$
>     in $J_i$ (and hence in $G_i$).
> (4) We apply (6.2) to $G_i$ and the model of $K_p$ and find a vertex $v$ of $G_i$ irrelevant to
>     the $\delta$-folio of $G_i$ relative to $Z$. We set $G_{i+1} = G_i \setminus v$ and return
>     for the next iteration.

Since no file imported here defines folios, the specification of Algorithm (6.5) is
expressed in terms of the inductive deletion trace `Alg65Trace`: starting from $H = G.\mathrm{cap}\ \delta$,
each step $r$ checks $|E(G_r)| > C |V(G_r)|$, finds a $K_p$-model $X_r$ in $J_r = G_r.\mathrm{toSimpleGraph}$
satisfying the output specification of (6.4), finds a branch index $i_r$, vertex $v_r \in X_r(i_r)$,
and separation $(V_A, V_B)$ satisfying conditions (i)–(iv) of (6.1) (the output specification of
(6.2)), and sets $G_{r+1} = G_r \setminus v_r$, terminating when $|E(G')| \le C |V(G')|$.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Parameters, Vertex Deletion on Subsets, and the Deletion Trace `Alg65Trace` -/

/-- Edge-density constant $C = \delta + 2(\delta + 1)2^{p - 3}$ in GM XIII (6.5) (page 87), where
$p = \lfloor 5\xi / 2 \rfloor + 3\delta + 1$ (`alg62Param ξ δ`). -/
def alg65Const (ξ δ : ℕ) : ℕ :=
  δ + 2 * (δ + 1) * 2 ^ (alg62Param ξ δ - 3)

/-- Pull back a vertex subset `Z ⊆ Fin (n' + 1)` to `Fin n'` after deleting vertex `v₀ : Fin (n' + 1)`. -/
def deleteVertexFinset {n' : ℕ} (Z : Finset (Fin (n' + 1))) (v₀ : Fin (n' + 1)) :
    Finset (Fin n') :=
  Finset.univ.filter (fun u : Fin n' => v₀.succAbove u ∈ Z)

@[simp]
theorem mem_deleteVertexFinset {n' : ℕ} (Z : Finset (Fin (n' + 1))) (v₀ : Fin (n' + 1))
    (u : Fin n') :
    u ∈ deleteVertexFinset Z v₀ ↔ v₀.succAbove u ∈ Z := by
  simp [deleteVertexFinset]

theorem image_succAbove_deleteVertexFinset {n' : ℕ} {Z : Finset (Fin (n' + 1))}
    {v₀ : Fin (n' + 1)} (hv₀ : v₀ ∉ Z) :
    (deleteVertexFinset Z v₀).image v₀.succAbove = Z := by
  ext x
  simp only [Finset.mem_image, mem_deleteVertexFinset]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hx
    have hne : x ≠ v₀ := fun h => hv₀ (h ▸ hx)
    rcases Fin.exists_succAbove_eq hne with ⟨u, rfl⟩
    exact ⟨u, hx, rfl⟩

theorem image_comp_succAbove_deleteVertexFinset {n₀ n' : ℕ} {Z : Finset (Fin (n' + 1))}
    {v₀ : Fin (n' + 1)} (emb : Fin (n' + 1) → Fin n₀) (hv₀ : v₀ ∉ Z) :
    (deleteVertexFinset Z v₀).image (emb ∘ v₀.succAbove) = Z.image emb := by
  rw [← Finset.image_image, image_succAbove_deleteVertexFinset hv₀]

theorem card_deleteVertexFinset_of_notMem {n' : ℕ} {Z : Finset (Fin (n' + 1))}
    {v₀ : Fin (n' + 1)} (hv₀ : v₀ ∉ Z) :
    (deleteVertexFinset Z v₀).card = Z.card := by
  calc (deleteVertexFinset Z v₀).card
    _ = ((deleteVertexFinset Z v₀).image v₀.succAbove).card :=
      (Finset.card_image_of_injective _ (Fin.strictMono_succAbove v₀).injective).symm
    _ = Z.card := by rw [image_succAbove_deleteVertexFinset hv₀]

theorem bitSetList_deleteVertexFinset {n' : ℕ} (Z : Finset (Fin (n' + 1))) (v₀ : Fin (n' + 1)) :
    bitSetList (deleteVertexFinset Z v₀) =
      List.ofFn ((fun u : Fin (n' + 1) => if u ∈ Z then 1 else 0) ∘ v₀.succAbove) := by
  simp [bitSetList, Function.comp_def]

/-- In GM XIII (6.2) / (6.1), the chosen vertex `v ∈ X i` never belongs to `Z`, because condition (i)
of `IsAlg61Separation` requires `Z ⊆ V_A` and `Disjoint V_A (X i)`. -/
theorem notMem_Z_of_isAlg61Separation {n p : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)}
    {X : Fin p → Finset (Fin n)} {i : Fin p} {v : Fin n} {V_A V_B : Finset (Fin n)}
    (hv : v ∈ X i) (hsep : IsAlg61Separation G Z p X i V_A V_B) :
    v ∉ Z := by
  intro hvZ
  have hvA : v ∈ V_A := hsep.2.2.1 hvZ
  exact Finset.disjoint_left.mp hsep.2.1 hvA hv

theorem two_pow_le_eight_mul_two_pow_sub_three (q : ℕ) :
    2 ^ q ≤ 8 * 2 ^ (q - 3) := by
  rcases q with _ | _ | _ | q
  · decide
  · decide
  · decide
  · rw [show q + 1 + 1 + 1 - 3 = q by omega,
        show q + 1 + 1 + 1 = q + 3 by omega,
        Nat.pow_add]
    omega

/-- Step (3) edge-count inequality of GM XIII (6.5) (page 87):
if `G_r` has at most `δ` loops at each vertex, at most `δ + 1` edges from `u` to `v` for all
`u ≠ v`, and `alg65Const ξ δ * n_r < G_r.numEdges`, then the underlying simple graph
`J_r = G_r.toSimpleGraph` satisfies `0 < n_r`,
`2 ^ (alg62Param ξ δ - 3) * n_r < J_r.edgeFinset.card`, and
`2 ^ (alg62Param ξ δ) * n_r ≤ 8 * J_r.edgeFinset.card`. -/
theorem alg65_step3_hedges {n_r : ℕ} (ξ δ : ℕ) (G_r : MultiDigraph n_r)
    (hloop : ∀ u : Fin n_r, G_r.edgeMult u u ≤ δ)
    (hnonloop : ∀ u v : Fin n_r, u ≠ v → G_r.edgeMult u v ≤ δ + 1)
    (hgt : alg65Const ξ δ * n_r < G_r.numEdges) :
    0 < n_r ∧
    2 ^ (alg62Param ξ δ - 3) * n_r < G_r.toSimpleGraph.edgeFinset.card ∧
    2 ^ (alg62Param ξ δ) * n_r ≤ 8 * G_r.toSimpleGraph.edgeFinset.card := by
  have hn_pos : 0 < n_r := by
    by_contra h0
    have hn0 : n_r = 0 := by omega
    subst hn0
    have hnum0 : G_r.numEdges = 0 := by simp [MultiDigraph.numEdges]
    omega
  have hle := G_r.numEdges_le_of_loop_and_nonloop_le hloop hnonloop
  let p := alg62Param ξ δ
  have hlt_combined :
      (δ + 2 * (δ + 1) * 2 ^ (p - 3)) * n_r <
        δ * n_r + 2 * (δ + 1) * G_r.toSimpleGraph.edgeFinset.card :=
    Nat.lt_of_lt_of_le hgt hle
  rw [Nat.add_mul, Nat.mul_assoc (2 * (δ + 1)) (2 ^ (p - 3)) n_r] at hlt_combined
  have h1 : 2 ^ (p - 3) * n_r < G_r.toSimpleGraph.edgeFinset.card := by
    have hpos : 0 < 2 * (δ + 1) := by omega
    have hlt_mul : 2 * (δ + 1) * (2 ^ (p - 3) * n_r) <
        2 * (δ + 1) * G_r.toSimpleGraph.edgeFinset.card := by omega
    exact (Nat.mul_lt_mul_left hpos).mp hlt_mul
  have hpow8 : 2 ^ p ≤ 8 * 2 ^ (p - 3) := two_pow_le_eight_mul_two_pow_sub_three p
  have h2 : 2 ^ p * n_r ≤ 8 * G_r.toSimpleGraph.edgeFinset.card := by
    have hmul : 2 ^ p * n_r ≤ (8 * 2 ^ (p - 3)) * n_r :=
      Nat.mul_le_mul_right n_r hpow8
    rw [Nat.mul_assoc] at hmul
    have hcard_le : 8 * (2 ^ (p - 3) * n_r) ≤ 8 * G_r.toSimpleGraph.edgeFinset.card :=
      Nat.mul_le_mul_left 8 (Nat.le_of_lt h1)
    exact le_trans hmul hcard_le
  exact ⟨hn_pos, h1, h2⟩

/-- Inductive deletion trace for GM XIII Algorithm (6.5):
starting from `H = G.cap δ` and `Z₀ = Z` with identity vertex embedding `id : Fin n₀ → Fin n₀`,
each recursion step (when `alg65Const ξ δ * (n' + 1) < G_r.numEdges`) witnesses:
- a `K_p`-model `X_r` in the underlying simple graph `G_r.toSimpleGraph` (Step (3), by (6.4)),
- a branch index `i_r`, vertex `v_r ∈ X_r i_r`, and separation `(VA_r, VB_r)` satisfying
  `IsAlg61Separation G_r Z_r p X_r i_r VA_r VB_r` (Step (4), by (6.2)),
and transitions to `G_{r+1} = G_r.deleteVertex v_r`, `Z_{r+1} = deleteVertexFinset Z_r v_r`,
and `emb_{r+1} = emb_r ∘ v_r.succAbove`. -/
inductive Alg65Trace (ξ δ : ℕ) {n₀ : ℕ} (H : MultiDigraph n₀) (Z₀ : Finset (Fin n₀)) :
    ∀ {n : ℕ}, MultiDigraph n → Finset (Fin n) → (Fin n → Fin n₀) → Prop where
  | refl : Alg65Trace ξ δ H Z₀ H Z₀ id
  | step {n' : ℕ} {G_r : MultiDigraph (n' + 1)} {Z_r : Finset (Fin (n' + 1))}
      {emb_r : Fin (n' + 1) → Fin n₀}
      (X_r : Fin (alg62Param ξ δ) → Finset (Fin (n' + 1)))
      (i_r : Fin (alg62Param ξ δ)) (v_r : Fin (n' + 1))
      (VA_r VB_r : Finset (Fin (n' + 1))) :
      Alg65Trace ξ δ H Z₀ G_r Z_r emb_r →
      alg65Const ξ δ * (n' + 1) < G_r.numEdges →
      IsCliqueModel G_r.toSimpleGraph (alg62Param ξ δ) X_r →
      v_r ∈ X_r i_r →
      IsAlg61Separation G_r Z_r (alg62Param ξ δ) X_r i_r VA_r VB_r →
      Alg65Trace ξ δ H Z₀
        (G_r.deleteVertex v_r) (deleteVertexFinset Z_r v_r) (emb_r ∘ v_r.succAbove)

namespace Alg65Trace

theorem induce_eq {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    G_r = H.induce emb_r := by
  induction htr with
  | refl => ext i j; rfl
  | step _ _ _ _ _ _ _ _ _ _ ih =>
    rw [ih]
    rfl

theorem injective_emb {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    Function.Injective emb_r := by
  induction htr with
  | refl => exact Function.injective_id
  | step _ _ v_r _ _ _ _ _ _ _ ih =>
    exact ih.comp (Fin.strictMono_succAbove v_r).injective

theorem strictMono_emb {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    StrictMono emb_r := by
  induction htr with
  | refl => exact strictMono_id
  | step _ _ v_r _ _ _ _ _ _ _ ih =>
    exact ih.comp (Fin.strictMono_succAbove v_r)

theorem image_Z {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    Z_r.image emb_r = Z₀ := by
  induction htr with
  | refl => simp
  | @step n' G_r' Z_r' emb_r' X_r i_r v_r VA_r VB_r _ _ _ hv_r hsep ih =>
    have hv_notZ : v_r ∉ Z_r' := notMem_Z_of_isAlg61Separation hv_r hsep
    rw [image_comp_succAbove_deleteVertexFinset emb_r' hv_notZ, ih]

theorem subset_image_univ {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    Z₀ ⊆ Finset.univ.image emb_r := by
  rw [← htr.image_Z]
  exact Finset.image_subset_image (Finset.subset_univ _)

theorem card_Z {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    Z_r.card = Z₀.card := by
  rw [← htr.image_Z, Finset.card_image_of_injective _ htr.injective_emb]

theorem le_num_vertices {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    n ≤ n₀ := by
  have h := Fintype.card_le_of_injective emb_r htr.injective_emb
  simpa using h

theorem numActivePairs_le {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    G_r.numActivePairs ≤ H.numActivePairs := by
  induction htr with
  | refl => exact le_rfl
  | @step n' G_r' Z_r' emb_r' X_r i_r v_r VA_r VB_r _ _ _ _ _ ih =>
    have hdel : (G_r'.deleteVertex v_r).numActivePairs ≤ G_r'.numActivePairs := by
      rw [MultiDigraph.numActivePairs_deleteVertex, MultiDigraph.numActivePairs]
      exact List.length_filter_le _ _
    exact le_trans hdel ih

theorem sumEdgeMultAvoiding_le_sumEdgeMult {n' : ℕ} (G : MultiDigraph (n' + 1))
    (v₀ : Fin (n' + 1)) (ps : List (Fin (n' + 1) × Fin (n' + 1))) :
    G.sumEdgeMultAvoiding v₀ ps ≤ G.sumEdgeMult ps := by
  induction ps with
  | nil => simp [MultiDigraph.sumEdgeMultAvoiding, MultiDigraph.sumEdgeMult]
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    simp only [MultiDigraph.sumEdgeMultAvoiding, MultiDigraph.sumEdgeMult]
    split_ifs <;> omega

theorem numEdges_deleteVertex_le {n' : ℕ} (G : MultiDigraph (n' + 1)) (v₀ : Fin (n' + 1)) :
    (G.deleteVertex v₀).numEdges ≤ G.numEdges := by
  rw [← G.sumEdgeMultAvoiding_activePairsList v₀, ← G.sumEdgeMult_activePairsList]
  exact sumEdgeMultAvoiding_le_sumEdgeMult G v₀ G.activePairsList

theorem numEdges_le {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    G_r.numEdges ≤ H.numEdges := by
  induction htr with
  | refl => exact le_rfl
  | step _ _ v_r _ _ _ _ _ _ _ ih =>
    exact le_trans (numEdges_deleteVertex_le _ v_r) ih

theorem loop_le_of_cap {ξ δ n₀ n : ℕ} {G : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ (G.cap δ) Z₀ G_r Z_r emb_r) (u : Fin n) :
    G_r.edgeMult u u ≤ δ := by
  rw [htr.induce_eq, MultiDigraph.induce_edgeMult]
  exact G.cap_loop_le δ (emb_r u)

theorem nonloop_le_of_cap {ξ δ n₀ n : ℕ} {G : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ (G.cap δ) Z₀ G_r Z_r emb_r) {u v : Fin n} (hne : u ≠ v) :
    G_r.edgeMult u v ≤ δ + 1 := by
  rw [htr.induce_eq, MultiDigraph.induce_edgeMult]
  exact G.cap_nonloop_le δ (htr.injective_emb.ne hne)

theorem castCard_trans {q₁ q₂ q₃ δ : ℕ} (h₁ : q₁ = q₂) (h₂ : q₂ = q₃)
    (F : FolioSetRep q₁ δ) :
    (F.castCard h₁).castCard h₂ = F.castCard (h₁.trans h₂) := by
  subst h₁ h₂
  rfl

theorem forall_isDeltaFolioRep {ξ δ n₀ n : ℕ} {H : MultiDigraph n₀} {Z₀ : Finset (Fin n₀)}
    (hZ₀ : Z₀.card ≤ ξ)
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ H Z₀ G_r Z_r emb_r) :
    ∀ F : FolioSetRep Z₀.card δ,
      IsDeltaFolioRep δ H Z₀ F ↔
        IsDeltaFolioRep δ G_r Z_r (F.castCard htr.card_Z.symm) := by
  induction htr with
  | refl =>
    intro F
    rfl
  | @step n' G_r' Z_r' emb_r' X_r i_r v_r VA_r VB_r htr_prev _ hmodel hv_r hsep ih =>
    intro F
    have hZ_r' : Z_r'.card ≤ ξ := htr_prev.card_Z.symm ▸ hZ₀
    have hirr : GM13.IsIrrelevantVertex G_r'.toGMDigraph δ Z_r'.toNatSet v_r.1 :=
      isIrrelevantVertex_of_isAlg61Separation hZ_r' hmodel hv_r hsep
    have hv_notZ : v_r ∉ Z_r' := notMem_Z_of_isAlg61Separation hv_r hsep
    have hstep :=
      (isIrrelevantVertex_iff_forall_isDeltaFolioRep δ G_r' Z_r' v_r hv_notZ).mp hirr
        (F.castCard htr_prev.card_Z.symm)
    rw [castCard_trans] at hstep
    exact (ih F).trans hstep

theorem forall_isDeltaFolioRep_of_cap {ξ δ n₀ n : ℕ} {G : MultiDigraph n₀}
    {Z₀ : Finset (Fin n₀)} (hZ₀ : Z₀.card ≤ ξ)
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ (G.cap δ) Z₀ G_r Z_r emb_r) :
    ∀ F : FolioSetRep Z₀.card δ,
      IsDeltaFolioRep δ G Z₀ F ↔
        IsDeltaFolioRep δ G_r Z_r (F.castCard htr.card_Z.symm) :=
  fun F => (forall_isDeltaFolioRep_cap δ G Z₀ F).trans (htr.forall_isDeltaFolioRep hZ₀ F)

theorem hasSameDeltaFolioRel_of_cap {ξ δ n₀ n : ℕ} {G : MultiDigraph n₀}
    {Z₀ : Finset (Fin n₀)} (hZ₀ : Z₀.card ≤ ξ)
    {G_r : MultiDigraph n} {Z_r : Finset (Fin n)} {emb_r : Fin n → Fin n₀}
    (htr : Alg65Trace ξ δ (G.cap δ) Z₀ G_r Z_r emb_r) :
    GM13.HasSameDeltaFolioRel G.toGMDigraph (G_r.toEmbeddedGMDigraph emb_r) δ Z₀.toNatSet :=
  (hasSameDeltaFolioRel_toEmbeddedGMDigraph_iff_forall_isDeltaFolioRep δ G G_r
    htr.strictMono_emb htr.image_Z htr.card_Z).mpr (htr.forall_isDeltaFolioRep_of_cap hZ₀)

end Alg65Trace

/-! ### Section 2: Word RAM Helper Programs for Algorithm (6.5) -/

/-- Initialize array `a_dst` of length `r_n` to the identity map `[0, 1, …, n - 1]`, using loop
register `r_i`. -/
def initIdArrProg (a_dst : Arr) (r_n r_i : Reg) : Cmd :=
  .seq (.alloc a_dst (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (.write a_dst (.reg r_i) (.reg r_i))))

theorem initIdArrProg_exec {w n : ℕ} (a_dst : ℕ) (r_n r_i : ℕ)
    (hne_ni : r_n ≠ r_i)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State} (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (initIdArrProg a_dst r_n r_i) s s' t ∧
      t ≤ 11 * n + 6 ∧
      s'.arrs a_dst = List.ofFn (fun u : Fin n => u.1) ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_i → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_dst (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_dst (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (k : ℕ) (st : State) : Prop :=
    (∃ (hlen : (st.arrs a_dst).length = n),
      ∀ j : Fin n, j.1 < k →
        (st.arrs a_dst)[j.1]'(by rw [hlen]; exact j.2) = j.1) ∧
    st.regs r_n = n ∧
    st.regs r_i = k ∧
    (∀ a : ℕ, a ≠ a_dst → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_i → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨⟨by simp [s₂, s₁], fun _ hj => by omega⟩,
      by simp [s₂, s₁, State.setReg_regs_ne _ _ hne_ni, hrn],
      by simp [s₂],
      fun a ha => by simp [s₂, s₁, show (a : Arr) ≠ a_dst from ha],
      fun r hr => by simp [s₂, s₁, State.setReg_regs_ne _ _ hr]⟩
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_i (.reg r_n) (.write a_dst (.reg r_i) (.reg r_i))
      ⦃Inv n⦄ ≤ fun _ => 3 + n * (7 + 3) := by
    apply Triple.forUp_const Inv n 3 hw hn_w
    · intro k _ st ⟨_, hrn_k, hri_k, _, _⟩
      exact ⟨hri_k, by simp [Expr.eval, checkWord, hrn_k, hn_w]⟩
    · intro k hk st ⟨⟨hlen_k, hbuf_k⟩, hrn_k, hri_k, harr_other, hreg_other⟩
      have hk_w : k < 2 ^ w := by omega
      let st₁ := st.writeArr a_dst k k
      have hex_w : Exec w (.write a_dst (.reg r_i) (.reg r_i)) st st₁ 3 :=
        .write (by simp [Expr.eval, checkWord, hri_k, hk_w])
          (by simp [Expr.eval, checkWord, hri_k, hk_w])
          (by simp [hlen_k, hk])
      refine ⟨st₁, 3, hex_w, le_rfl,
        ⟨⟨by simp [st₁, hlen_k], fun j hj => ?_⟩,
         by simp [st₁, State.setReg_regs_ne _ _ hne_ni, hrn_k],
         by simp [st₁],
         fun a ha => by simp [st₁, show (a : Arr) ≠ a_dst from ha, harr_other a ha],
         fun r hr => by simp [st₁, State.setReg_regs_ne _ _ hr, hreg_other r hr]⟩,
        by simp [st₁, hri_k]⟩
      simp only [st₁, State.setReg_arrs, State.writeArr_arrs_self]
      by_cases hjk : j.1 = k
      · subst hjk
        exact List.getElem_set_self _
      · rw [List.getElem_set_ne (Ne.symm hjk)]
        exact hbuf_k j (by omega)
  rcases hLoop s₂ hInv₀ with
    ⟨s₃, t₃, hex₃, ht₃, ⟨hlen₃, hbuf₃⟩, _, _, harr₃, hreg₃⟩
  dsimp only at ht₃
  have hdst₃ : s₃.arrs a_dst = List.ofFn (fun u : Fin n => u.1) := by
    apply List.ext_getElem
    · simp [hlen₃]
    · intro i hi₁ hi₂
      rw [List.getElem_ofFn]
      exact hbuf₃ ⟨i, by omega⟩ (by omega)
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hdst₃, harr₃, hreg₃⟩

/-- Wrapper around `readSliceProg_exec` at offset `0` that copies an entire list `l` of length `n`
from `a_src` into `a_dst` in `O(n + 1)` steps. -/
theorem copyListProg_exec {w n : ℕ} (a_src a_dst : ℕ) (r_n r_base : ℕ)
    (hne_arr : a_src ≠ a_dst) (hr_n : r_n < r_base)
    (l : List ℕ) (hlen : l.length = n) (hl_w : ∀ x ∈ l, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State} (hsrc : s.arrs a_src = l) (hrn_val : s.regs r_n = n) :
    ∃ s' t,
      Exec w (readSliceProg a_src (.const 0) a_dst (.reg r_n) r_base) s s' t ∧
      t ≤ 16 * n + 9 ∧
      s'.arrs a_dst = l ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hoff_n_w : 0 + n < 2 ^ w := by omega
  have hsrc' : s.arrs a_src = [] ++ l ++ [] := by simp [hsrc]
  rcases readSliceProg_exec a_src a_dst (.const 0) r_n r_base
      hne_arr hr_n [] l [] rfl hlen hl_w hw hoff_n_w
      (by simp [Expr.eval, checkWord, h0_w]) hsrc' hrn_val with
    ⟨s', t, hex, ht, hdst, harr, hreg⟩
  dsimp [Expr.cost] at ht
  exact ⟨s', t, hex, by omega, hdst, harr, hreg⟩

theorem not_mem_writtenRegs_toSimpleGraphEdgeListProg (a_src a_buf a_dst : Arr)
    {r : ℕ} (hr : 10 ≤ r) :
    (r : Reg) ∉ (toSimpleGraphEdgeListProg a_src a_buf a_dst 0).writtenRegs := by
  simp [toSimpleGraphEdgeListProg, toSimpleGraphEdgeListBody, readTripleEndpoints,
    bufPush2, readSliceProg, readSliceBody, forUp, Cmd.writtenRegs,
    show (r : Reg) ≠ 0 by omega,
    show (r : Reg) ≠ 1 by omega,
    show (r : Reg) ≠ 2 by omega,
    show (r : Reg) ≠ 3 by omega,
    show (r : Reg) ≠ 4 by omega,
    show (r : Reg) ≠ 5 by omega,
    show (r : Reg) ≠ 6 by omega,
    show (r : Reg) ≠ 7 by omega,
    show (r : Reg) ≠ 8 by omega,
    show (r : Reg) ≠ 9 by omega]

theorem not_mem_writtenRegs_toSimpleGraphProg (a_src a_buf a_deg a_start a_end a_entries : Arr)
    {r : ℕ} (hr : 10 ≤ r) :
    (r : Reg) ∉
      (toSimpleGraphProg a_src a_buf a_deg a_start a_end a_entries 0).writtenRegs := by
  simp [toSimpleGraphProg, toSimpleGraphEdgeListProg, toSimpleGraphEdgeListBody,
    readTripleEndpoints, bufPush2, readSliceProg, readSliceBody,
    parseGraphProg, parsePass1Body, parsePrefixBody, parsePass2Body,
    readEdgeEndpoints, incArrAt, csrAppend, listAppend, forUp, Cmd.writtenRegs,
    show (r : Reg) ≠ 0 by omega,
    show (r : Reg) ≠ 1 by omega,
    show (r : Reg) ≠ 2 by omega,
    show (r : Reg) ≠ 3 by omega,
    show (r : Reg) ≠ 4 by omega,
    show (r : Reg) ≠ 5 by omega,
    show (r : Reg) ≠ 6 by omega,
    show (r : Reg) ≠ 7 by omega,
    show (r : Reg) ≠ 8 by omega,
    show (r : Reg) ≠ 9 by omega]

/-- Pack `G_r.enc` (from array `18 + p`, where `r_27 = G_r.numActivePairs`) followed by
`List.ofFn (fun u : Fin n_r => (emb_r u).1)` (from array `18 + p + 2`, where `r_26 = n_r`)
into `outArr = 1`. -/
def alg65WriteOutProg (p : ℕ) : Cmd :=
  .seq (.assign 20 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27))))
    (.seq (.assign 21 (.op .add (.reg 20) (.reg 26)))
      (.seq (.alloc outArr (.reg 21))
        (.seq (.assign 14 (.reg 20))
          (.seq (.assign 15 (.op .mul (.const 2) (.reg 14)))
            (.seq (.assign 16 (.const 0))
              (.seq (copyToOutProg (18 + p) (.const 0) 2)
                (.seq (.assign 14 (.reg 26))
                  (.seq (.assign 15 (.op .mul (.const 2) (.reg 14)))
                    (.seq (.assign 16 (.const 0))
                      (copyToOutProg (18 + p + 2) (.reg 20) 2))))))))))

theorem alg65WriteOutProg_exec {w n₀ n_r : ℕ} (p : ℕ)
    (G_r : MultiDigraph n_r) (emb_r : Fin n_r → Fin n₀)
    (hw3 : 3 < 2 ^ w) (hn₀_w : n₀ < 2 ^ w) (hn_w : n_r < 2 ^ w)
    (hm3_w : 2 + 3 * G_r.numActivePairs < 2 ^ w)
    (h2len_w : 2 * (2 + 3 * G_r.numActivePairs + n_r) < 2 ^ w)
    (hedges_w : G_r.numEdges < 2 ^ w)
    {s : State}
    (hG_arr : s.arrs (18 + p) = G_r.enc)
    (hemb_arr : s.arrs (18 + p + 2) = List.ofFn (fun u : Fin n_r => (emb_r u).1))
    (hr26 : s.regs 26 = n_r)
    (hr27 : s.regs 27 = G_r.numActivePairs) :
    ∃ s' t,
      Exec w (alg65WriteOutProg p) s s' t ∧
      t ≤ 54 * G_r.numActivePairs + 18 * n_r + 80 ∧
      s'.arrs outArr = G_r.enc ++ List.ofFn (fun u : Fin n_r => (emb_r u).1) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G_r.numActivePairs < 2 ^ w := by omega
  have h3m'_w : 3 * G_r.numActivePairs < 2 ^ w := by omega
  let len₁ := 2 + 3 * G_r.numActivePairs
  have hlen₁_def : len₁ = 2 + 3 * G_r.numActivePairs := rfl
  have hlen₁_eq : G_r.enc.length = len₁ := G_r.length_enc
  have hlen₁_w : len₁ < 2 ^ w := hm3_w
  have h2len₁_w : 2 * len₁ < 2 ^ w := by omega
  have htot_w : len₁ + n_r < 2 ^ w := by omega
  have h2n_w : 2 * n_r < 2 ^ w := by omega
  -- 1. r_20 := 2 + 3 * r_27
  let s₁ := s.setReg 20 len₁
  have hex₁ : Exec w (.assign 20 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27)))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr27, hw2, hw3, hm'_w, h3m'_w, hm3_w, len₁])
  -- 2. r_21 := r_20 + r_26
  let s₂ := s₁.setReg 21 (len₁ + n_r)
  have hex₂ : Exec w (.assign 21 (.op .add (.reg 20) (.reg 26))) s₁ s₂ 4 :=
    .assign (by simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr26, hlen₁_w, hn_w, htot_w])
  -- 3. alloc outArr (.reg 21)
  let s₃ := s₂.setArr outArr (List.replicate (len₁ + n_r) 0)
  have hex₃ : Exec w (.alloc outArr (.reg 21)) s₂ s₃ (1 + (len₁ + n_r)) :=
    .alloc (by simp [s₂, Expr.eval, checkWord, htot_w])
  -- 4. r_14 := r_20, r_15 := 2 * r_14, r_16 := 0
  let s₄ := s₃.setReg 14 len₁
  have hex₄ : Exec w (.assign 14 (.reg 20)) s₃ s₄ 2 :=
    .assign (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hlen₁_w])
  let s₅ := s₄.setReg 15 (2 * len₁)
  have hex₅ : Exec w (.assign 15 (.op .mul (.const 2) (.reg 14))) s₄ s₅ 4 :=
    .assign (by simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hlen₁_w, h2len₁_w])
  let s₆ := s₅.setReg 16 0
  have hex₆ : Exec w (.assign 16 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hconst₆ : ConstRegs len₁ 0 2 s₆ :=
    ⟨by simp [s₆, s₅, s₄, State.setReg],
     by simp [s₆, s₅, s₄, State.setReg],
     by simp [s₆]⟩
  have henc_w : ∀ x ∈ G_r.enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact hm'_w
    · exact all_lt_flatTriples G_r G_r.activePairsList hn_w
        (fun q _ => Nat.lt_of_le_of_lt (G_r.edgeMult_le_numEdges q.1 q.2) hedges_w) x hx
  have hout₆ : s₆.arrs outArr = [] ++ List.replicate len₁ 0 ++ List.replicate n_r 0 := by
    simp only [s₆, s₅, s₄, s₃, State.setReg_arrs, State.setArr_arrs_self, List.nil_append]
    exact List.replicate_add len₁ n_r 0
  have harr_G₆ : s₆.arrs (18 + p) = G_r.enc := by
    simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_arrs]
    rw [State.setArr_arrs_ne _ _ (by dsimp [Arr, outArr]; omega)]
    exact hG_arr
  -- 5. copyToOutProg (18 + p) (.const 0) 2
  have hoff1_w : 0 + len₁ < 2 ^ w := by omega
  rcases copyToOutProg_exec 0 (18 + p) (.const 0) 2 (by dsimp [Arr, outArr]; omega)
      [] G_r.enc (List.replicate n_r 0)
      rfl hlen₁_eq henc_w hw hoff1_w hconst₆
      (by simp [Expr.eval, checkWord, h0_w]) harr_G₆ hout₆ with
    ⟨s₇, t₇, hex₇, ht₇, _, hout₇, harr₇, hreg₇⟩
  dsimp [Expr.cost] at ht₇
  have hr20_7 : s₇.regs 20 = len₁ := by
    rw [hreg₇ 20 (by omega)]
    simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg]
  have hr26_7 : s₇.regs 26 = n_r := by
    rw [hreg₇ 26 (by omega)]
    simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hr26]
  have hemb_7 : s₇.arrs (18 + p + 2) = List.ofFn (fun u : Fin n_r => (emb_r u).1) := by
    rw [harr₇ (18 + p + 2) (by dsimp [Arr, outArr]; omega)]
    simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_arrs]
    rw [State.setArr_arrs_ne _ _ (by dsimp [Arr, outArr]; omega)]
    exact hemb_arr
  -- 6. r_14 := r_26, r_15 := 2 * r_14, r_16 := 0
  let s₈ := s₇.setReg 14 n_r
  have hex₈ : Exec w (.assign 14 (.reg 26)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr26_7, hn_w])
  let s₉ := s₈.setReg 15 (2 * n_r)
  have hex₉ : Exec w (.assign 15 (.op .mul (.const 2) (.reg 14))) s₈ s₉ 4 :=
    .assign (by simp [s₈, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hn_w, h2n_w])
  let s₁₀ := s₉.setReg 16 0
  have hex₁₀ : Exec w (.assign 16 (.const 0)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hconst₁₀ : ConstRegs n_r 0 2 s₁₀ :=
    ⟨by simp [s₁₀, s₉, s₈, State.setReg],
     by simp [s₁₀, s₉, State.setReg],
     by simp [s₁₀]⟩
  have hemb_w : ∀ x ∈ List.ofFn (fun u : Fin n_r => (emb_r u).1), x < 2 ^ w := by
    intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨u, rfl⟩
    exact Nat.lt_trans (emb_r u).2 hn₀_w
  have hout₁₀ : s₁₀.arrs outArr = G_r.enc ++ List.replicate n_r 0 ++ [] := by
    simpa [s₁₀, s₉, s₈] using hout₇
  have hemb₁₀ : s₁₀.arrs (18 + p + 2) = List.ofFn (fun u : Fin n_r => (emb_r u).1) := by
    simpa [s₁₀, s₉, s₈] using hemb_7
  -- 7. copyToOutProg (18 + p + 2) (.reg 20) 2
  rcases copyToOutProg_exec len₁ (18 + p + 2) (.reg 20) 2 (by dsimp [Arr, outArr]; omega)
      G_r.enc (List.ofFn (fun u : Fin n_r => (emb_r u).1)) []
      hlen₁_eq (by simp) hemb_w hw htot_w hconst₁₀
      (by simp [s₁₀, s₉, s₈, State.setReg, Expr.eval, checkWord, hr20_7, hlen₁_w])
      hemb₁₀ hout₁₀ with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, _, hout₁₁, _, _⟩
  dsimp [Expr.cost] at ht₁₁
  refine ⟨s₁₁, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))),
    by omega,
    by simpa using hout₁₁⟩

/-! ### Section 3: Main Recursion Loop of Algorithm (6.5) (`alg65LoopProg`) -/

/-- Problem input for GM XIII Algorithm (6.5) with fixed parameters `ξ, δ : ℕ`:
a multi-digraph `G : MultiDigraph n` and a subset `Z ⊆ V(G)` with `|Z| ≤ ξ`. -/
structure Alg65Input (ξ δ : ℕ) where
  /-- Number of vertices `v = |V(G)|`. -/
  n : ℕ
  /-- Input multi-digraph on `Fin n`. -/
  G : MultiDigraph n
  /-- Terminal vertex subset `Z ⊆ V(G)`. -/
  Z : Finset (Fin n)
  /-- Cardinality bound `|Z| ≤ ξ`. -/
  hZ : Z.card ≤ ξ

/-- Input size for GM XIII Algorithm (6.5): `v = |V(G)| = x.n`. -/
def alg65Size {ξ δ : ℕ} (x : Alg65Input ξ δ) : ℕ :=
  x.n

/-- Flat input encoding of `x : Alg65Input ξ δ` in `inArr`: `x.G.enc ++ bitSetList x.Z`. -/
def encAlg65In {ξ δ : ℕ} (x : Alg65Input ξ δ) : List ℕ :=
  x.G.enc ++ bitSetList x.Z

/-- Step-constant for `alg64InMemProg p`. -/
def alg64StepConst (p : ℕ) : ℕ :=
  let fac := 2 ^ (p - 3)
  400 + 500 * p + 500 * fac + 500 * (p * fac)

/-- Per-iteration step-count constant for `alg65LoopBody ξ δ` relative to `(x.n + 1) ^ 2`. -/
def alg65IterConst (ξ δ : ℕ) : ℕ :=
  let p := alg62Param ξ δ
  1200 + alg64StepConst p + p * (ξ + 1) * 800

/-- Loop invariant at the start of each iteration of `alg65LoopProg ξ δ`. -/
structure Alg65LoopState (ξ δ : ℕ) (x : Alg65Input ξ δ)
    (n_r : ℕ) (G_r : MultiDigraph n_r) (Z_r : Finset (Fin n_r))
    (emb_r : Fin n_r → Fin x.n) (s : State) : Prop where
  trace : Alg65Trace ξ δ (x.G.cap δ) x.Z G_r Z_r emb_r
  hG_arr : s.arrs (18 + alg62Param ξ δ) = G_r.enc
  hZ_arr : s.arrs (18 + alg62Param ξ δ + 1) = bitSetList Z_r
  hemb_arr : s.arrs (18 + alg62Param ξ δ + 2) = List.ofFn (fun u : Fin n_r => (emb_r u).1)
  hr26 : s.regs 26 = n_r
  hr27 : s.regs 27 = G_r.numActivePairs
  hr28 : s.regs 28 = G_r.numEdges

/-- Body of one iteration of GM XIII Algorithm (6.5) Steps (3)–(4):
1. Builds `encGraph G_r.toSimpleGraph` in `inArr` (`toSimpleGraphEdgeListProg`) and runs
   `alg64InMemProg p` to obtain a `K_p`-model `X_r` in arrays `18 .. 18 + p - 1`.
2. Builds the CSR representation of `G_r.toSimpleGraph` in arrays `(3, 4, 5)` (`toSimpleGraphProg`).
3. Copies `Z_r`, `emb_r`, and `G_r.enc` from `(18 + p + 1, 18 + p + 2, 18 + p)` into `(9, 16, 17)`,
   sets `r_14 := r_26` and `r_19 := 2 * r_1`, and runs `alg62CoreProg ξ δ` to obtain `v_r` in `r_25`.
4. Deletes `v_r` from `G_r` (`deleteVertexMultiDigraphProg`), `Z_r` (`deleteNthArrProg`), and
   `emb_r` (`deleteNthArrProg`), storing the updated `(G_{r+1}, Z_{r+1}, emb_{r+1})` back in
   arrays `(18 + p, 18 + p + 1, 18 + p + 2)` and updating `r_26, r_27, r_28`. -/
def alg65LoopBody (ξ δ : ℕ) : Cmd :=
  let p := alg62Param ξ δ
  .seq (toSimpleGraphEdgeListProg (18 + p) 2 inArr 0)
    (.seq (alg64InMemProg p)
      (.seq (toSimpleGraphProg (18 + p) 2 6 3 4 5 0)
        (.seq (readSliceProg (18 + p + 1) (.const 0) 9 (.reg 26) 29)
          (.seq (readSliceProg (18 + p + 2) (.const 0) 16 (.reg 26) 29)
            (.seq (.assign 29 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27))))
              (.seq (readSliceProg (18 + p) (.const 0) 17 (.reg 29) 30)
                (.seq (.assign 14 (.reg 26))
                  (.seq (.assign 19 (.op .mul (.const 2) (.reg 1)))
                    (.seq (alg62CoreProg ξ δ)
                      (.seq (deleteVertexMultiDigraphProg 17 2 (18 + p) 25 26)
                        (.seq (deleteNthArrProg 9 2 26 25 29)
                          (.seq (readSliceProg 9 (.const 0) (18 + p + 1) (.reg 26) 29)
                            (.seq (deleteNthArrProg 16 2 26 25 29)
                              (readSliceProg 16 (.const 0) (18 + p + 2) (.reg 26) 29))))))))))))))

/-- Main `.while` loop of GM XIII Algorithm (6.5) Step (2):
while `alg65Const ξ δ * |V(G_r)| < |E(G_r)|`, execute `alg65LoopBody ξ δ`. -/
def alg65LoopProg (ξ δ : ℕ) : Cmd :=
  .while (.op .lt (.op .mul (.const (alg65Const ξ δ)) (.reg 26)) (.reg 28))
    (alg65LoopBody ξ δ)

theorem alg65LoopBody_exec {w : ℕ} (ξ δ : ℕ) (x : Alg65Input ξ δ)
    (n' : ℕ) (G_r : MultiDigraph (n' + 1)) (Z_r : Finset (Fin (n' + 1)))
    (emb_r : Fin (n' + 1) → Fin x.n)
    (hw3 : 3 < 2 ^ w)
    (hn0_w : x.n < 2 ^ w)
    (h2n0_w : 2 * x.n < 2 ^ w)
    (hp_w : alg62Param ξ δ < 2 ^ w)
    (hm3_cap_w : 2 + 3 * (x.G.cap δ).numActivePairs < 2 ^ w)
    (hedges_cap_w : (x.G.cap δ).numEdges < 2 ^ w)
    (hpow_64_w : (x.n + 2) ^ (alg62Param ξ δ + 2) < 2 ^ w)
    (hgt : alg65Const ξ δ * (n' + 1) < G_r.numEdges)
    {s : State}
    (hst : Alg65LoopState ξ δ x (n' + 1) G_r Z_r emb_r s) :
    ∃ (G_next : MultiDigraph n') (Z_next : Finset (Fin n'))
      (emb_next : Fin n' → Fin x.n) (s' : State) (t : ℕ),
      Exec w (alg65LoopBody ξ δ) s s' t ∧
      t ≤ alg65IterConst ξ δ * (x.n + 1) ^ 2 ∧
      Alg65LoopState ξ δ x n' G_next Z_next emb_next s' := by
  let p := alg62Param ξ δ
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hnr_le : n' + 1 ≤ x.n := hst.trace.le_num_vertices
  have hnr_w : n' + 1 < 2 ^ w := by omega
  have hn'_w : n' < 2 ^ w := by omega
  have h2nr_w : 2 * (n' + 1) < 2 ^ w := by omega
  have hm'_le_cap : G_r.numActivePairs ≤ (x.G.cap δ).numActivePairs := hst.trace.numActivePairs_le
  have hcap_le_G : (x.G.cap δ).numActivePairs ≤ x.G.numActivePairs := by
    simp only [MultiDigraph.numActivePairs, MultiDigraph.activePairsList_cap]
    exact List.length_filter_le _ _
  have hm'_le_sq : G_r.numActivePairs ≤ x.n * x.n :=
    le_trans hm'_le_cap (le_trans hcap_le_G x.G.numActivePairs_le_sq)
  have hm3_w : 2 + 3 * G_r.numActivePairs < 2 ^ w := by omega
  have hm'_w : G_r.numActivePairs < 2 ^ w := by omega
  have hedges_r_le : G_r.numEdges ≤ (x.G.cap δ).numEdges := hst.trace.numEdges_le
  have hedges_r_w : G_r.numEdges < 2 ^ w := by omega
  -- Step 3 arithmetic: `G_r.toSimpleGraph` satisfies `Alg64Input p`
  have hloop_r : ∀ u : Fin (n' + 1), G_r.edgeMult u u ≤ δ := hst.trace.loop_le_of_cap
  have hnonloop_r : ∀ u v : Fin (n' + 1), u ≠ v → G_r.edgeMult u v ≤ δ + 1 :=
    fun u v hne => hst.trace.nonloop_le_of_cap hne
  obtain ⟨_, _, hedges_64⟩ := alg65_step3_hedges ξ δ G_r hloop_r hnonloop_r hgt
  let x64 : Alg64Input p := ⟨n' + 1, G_r.toSimpleGraph, by omega, hedges_64⟩
  have hpow_r_w : (x64.n + 2) ^ (p + 2) < 2 ^ w := by
    have hle : (n' + 1 + 2) ^ (p + 2) ≤ (x.n + 2) ^ (p + 2) :=
      Nat.pow_le_pow_left (by omega) (p + 2)
    exact Nat.lt_of_le_of_lt hle hpow_64_w
  -- 1. `toSimpleGraphEdgeListProg (18 + p) 2 inArr 0`
  have hG_src₀ : s.arrs (18 + p) = G_r.enc ++ [] := by
    rw [List.append_nil]; exact hst.hG_arr
  rcases toSimpleGraphEdgeListProg_exec G_r [] (18 + p) 2 inArr 0
      (by omega) (by dsimp [inArr]; omega) hw3 hnr_w hm3_w hG_src₀ with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, _, _, harr₁, _⟩
  have hreg₁ : ∀ r : ℕ, 10 ≤ r → s₁.regs r = s.regs r :=
    fun r hr => Exec.regs_eq_of_not_mem_writtenRegs hex₁
      (not_mem_writtenRegs_toSimpleGraphEdgeListProg (18 + p) 2 inArr hr)
  -- 2. `alg64InMemProg p`
  rcases alg64InMemProg_exec p x64 hpow_r_w hin₁ with
    ⟨s₂, t₂, X_r, hex₂, ht₂, _, hX_bits₂, hmodel_r, harr₂, hreg₂⟩
  change t₂ ≤ alg64StepConst p * (n' + 1 + 1) ^ 2 at ht₂
  -- 3. `toSimpleGraphProg (18 + p) 2 6 3 4 5 0`
  have hG_src₂ : s₂.arrs (18 + p) = G_r.enc ++ [] := by
    rw [harr₂ (18 + p) (Or.inr le_rfl), harr₁ (18 + p) (by omega) (by dsimp [inArr]; omega)]
    exact hG_src₀
  rcases toSimpleGraphProg_exec G_r [] (18 + p) 2 6 3 4 5 0
      (by omega) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw3 hnr_w hm3_w hG_src₂ with
    ⟨s₃, t₃, hex₃, ht₃, _, _, hr1_3, hadj_H₃, hent_H₃, harr₃, _⟩
  have hreg₃ : ∀ r : ℕ, 10 ≤ r → s₃.regs r = s₂.regs r :=
    fun r hr => Exec.regs_eq_of_not_mem_writtenRegs hex₃
      (not_mem_writtenRegs_toSimpleGraphProg (18 + p) 2 6 3 4 5 hr)
  let m_H := G_r.toSimpleGraph.edgeFinset.card
  have hm_H_eq : (edgeListOf G_r.toSimpleGraph).length = m_H :=
    length_edgeListOf_eq_card_edgeFinset G_r.toSimpleGraph
  rw [hm_H_eq] at hr1_3 hent_H₃
  have hm_H_le : m_H ≤ G_r.numActivePairs := by
    rw [← hm_H_eq, ← MultiDigraph.toSimplePairsAux_activePairsList]
    exact length_toSimplePairsAux_le (n' + 1) (n' + 1) G_r.activePairsList
  have hm_H_w : m_H < 2 ^ w := by omega
  have h2m_H_w : 2 * m_H < 2 ^ w := by omega
  have hr26_3 : s₃.regs 26 = n' + 1 := by
    rw [hreg₃ 26 (by omega), hreg₂ 26 (by omega), hreg₁ 26 (by omega), hst.hr26]
  have hr27_3 : s₃.regs 27 = G_r.numActivePairs := by
    rw [hreg₃ 27 (by omega), hreg₂ 27 (by omega), hreg₁ 27 (by omega), hst.hr27]
  have hr28_3 : s₃.regs 28 = G_r.numEdges := by
    rw [hreg₃ 28 (by omega), hreg₂ 28 (by omega), hreg₁ 28 (by omega), hst.hr28]
  have hZ_arr₃ : s₃.arrs (18 + p + 1) = bitSetList Z_r := by
    rw [harr₃ (18 + p + 1) (by omega) (by dsimp [inArr]; omega) (by omega) (by omega) (by omega) (by omega),
      harr₂ (18 + p + 1) (Or.inr (by omega)),
      harr₁ (18 + p + 1) (by omega) (by dsimp [inArr]; omega)]
    exact hst.hZ_arr
  have hemb_arr₃ : s₃.arrs (18 + p + 2) = List.ofFn (fun u : Fin (n' + 1) => (emb_r u).1) := by
    rw [harr₃ (18 + p + 2) (by omega) (by dsimp [inArr]; omega) (by omega) (by omega) (by omega) (by omega),
      harr₂ (18 + p + 2) (Or.inr (by omega)),
      harr₁ (18 + p + 2) (by omega) (by dsimp [inArr]; omega)]
    exact hst.hemb_arr
  have hG_arr₃ : s₃.arrs (18 + p) = G_r.enc := by
    rw [harr₃ (18 + p) (by omega) (by dsimp [inArr]; omega) (by omega) (by omega) (by omega) (by omega),
      harr₂ (18 + p) (Or.inr le_rfl),
      harr₁ (18 + p) (by omega) (by dsimp [inArr]; omega)]
    exact hst.hG_arr
  -- 4a. Copy `Z_r` from `18 + p + 1` to `9`
  have hZ_w : ∀ b ∈ bitSetList Z_r, b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one Z_r idx hidx
    omega
  rcases copyListProg_exec (18 + p + 1) 9 26 29 (by omega) (by omega)
      (bitSetList Z_r) (length_bitSetList Z_r) hZ_w hw hnr_w hZ_arr₃ hr26_3 with
    ⟨s₄, t₄, hex₄, ht₄, hZ_arr₄, harr₄, hreg₄⟩
  -- 4b. Copy `emb_r` from `18 + p + 2` to `16`
  have hemb_w : ∀ b ∈ List.ofFn (fun u : Fin (n' + 1) => (emb_r u).1), b < 2 ^ w := by
    intro b hb
    rw [List.mem_ofFn] at hb
    rcases hb with ⟨u, rfl⟩
    exact Nat.lt_trans (emb_r u).2 hn0_w
  rcases copyListProg_exec (18 + p + 2) 16 26 29 (by omega) (by omega)
      (List.ofFn (fun u : Fin (n' + 1) => (emb_r u).1)) (by simp) hemb_w hw hnr_w
      (by rw [harr₄ (18 + p + 2) (by omega)]; exact hemb_arr₃)
      (by rw [hreg₄ 26 (by omega)]; exact hr26_3) with
    ⟨s₅, t₅, hex₅, ht₅, hemb_arr₅, harr₅, hreg₅⟩
  -- 4c. Set `r_29 := 2 + 3 * r_27` and copy `G_r.enc` from `18 + p` to `17`
  have hr27_5 : s₅.regs 27 = G_r.numActivePairs := by
    rw [hreg₅ 27 (by omega), hreg₄ 27 (by omega)]; exact hr27_3
  let s₆ := s₅.setReg 29 (2 + 3 * G_r.numActivePairs)
  have hex₆ : Exec w (.assign 29 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27)))) s₅ s₆ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr27_5, hw2, hw3, hm'_w, show 3 * G_r.numActivePairs < 2 ^ w by omega, hm3_w])
  have henc_w : ∀ b ∈ G_r.enc, b < 2 ^ w := by
    intro b hb
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact hnr_w
    · exact hm'_w
    · exact all_lt_flatTriples G_r G_r.activePairsList hnr_w
        (fun q _ => Nat.lt_of_le_of_lt (G_r.edgeMult_le_numEdges q.1 q.2) hedges_r_w) b hb
  rcases copyListProg_exec (18 + p) 17 29 30 (by omega) (by omega)
      G_r.enc G_r.length_enc henc_w hw hm3_w (s := s₆)
      (by change s₅.arrs (18 + p) = G_r.enc; rw [harr₅ (18 + p) (by omega), harr₄ (18 + p) (by omega)]; exact hG_arr₃)
      (by simp [s₆]) with
    ⟨s₇, t₇, hex₇, ht₇, hG_arr₇, harr₇, hreg₇⟩
  -- 4d. Set `r_14 := r_26` and `r_19 := 2 * r_1`
  have hr26_7 : s₇.regs 26 = n' + 1 := by
    rw [hreg₇ 26 (by omega)]
    change s₅.regs 26 = n' + 1
    rw [hreg₅ 26 (by omega), hreg₄ 26 (by omega), hr26_3]
  have hr1_7 : s₇.regs 1 = m_H := by
    rw [hreg₇ 1 (by omega)]
    change s₅.regs 1 = m_H
    rw [hreg₅ 1 (by omega), hreg₄ 1 (by omega), hr1_3]
  let s₈ := s₇.setReg 14 (n' + 1)
  have hex₈ : Exec w (.assign 14 (.reg 26)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr26_7, hnr_w])
  let s₉ := s₈.setReg 19 (2 * m_H)
  have hex₉ : Exec w (.assign 19 (.op .mul (.const 2) (.reg 1))) s₈ s₉ 4 :=
    .assign (by simp [s₈, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr1_7, hw2, hm_H_w, h2m_H_w])
  -- 4e. Run `alg62CoreProg ξ δ`
  have hZ_card_r : Z_r.card ≤ ξ := by
    rw [hst.trace.card_Z]
    exact x.hZ
  have harr_lt6_9 : ∀ a : ℕ, a < 6 → s₉.arrs a = s₃.arrs a := by
    intro a ha
    change s₇.arrs a = s₃.arrs a
    rw [harr₇ a (by omega)]
    change s₅.arrs a = s₃.arrs a
    rw [harr₅ a (by omega), harr₄ a (by omega)]
  have hadj_H₉ : IsAdjList G_r.toSimpleGraph 3 4 5 (edgeNeighbors (edgeListOf G_r.toSimpleGraph)) s₉ :=
    hadj_H₃.of_arrs_eq (harr_lt6_9 3 (by decide)) (harr_lt6_9 4 (by decide)) (harr_lt6_9 5 (by decide))
  have hent_H₉ : (s₉.arrs 5).length < 2 ^ w := by
    rw [harr_lt6_9 5 (by decide), hent_H₃]
    exact h2m_H_w
  have hZ_bit₉ : IsBitSet Z_r 9 s₉ := by
    apply IsBitSet.of_bitSetList
    change s₇.arrs 9 = bitSetList Z_r
    rw [harr₇ 9 (by omega)]
    change s₅.arrs 9 = bitSetList Z_r
    rw [harr₅ 9 (by omega), hZ_arr₄]
  have hX_bits₉ : ∀ k : Fin p, IsBitSet (X_r k) (18 + k.1) s₉ := by
    intro k
    refine (hX_bits₂ k).of_arr_eq ?_
    change s₇.arrs (18 + k.1) = s₂.arrs (18 + k.1)
    rw [harr₇ (18 + k.1) (by omega)]
    change s₅.arrs (18 + k.1) = s₂.arrs (18 + k.1)
    rw [harr₅ (18 + k.1) (by omega), harr₄ (18 + k.1) (by omega),
      harr₃ (18 + k.1) (by omega) (by dsimp [inArr]; omega) (by omega) (by omega) (by omega) (by omega)]
  rcases alg62CoreProg_exec ξ δ G_r (edgeNeighbors (edgeListOf G_r.toSimpleGraph))
      Z_r X_r (2 * m_H) hZ_card_r hmodel_r
      hw2 h2nr_w hp_w h2m_H_w le_rfl
      (s := s₉) (by simp [s₉, s₈, State.setReg]) (by simp [s₉])
      hadj_H₉ hent_H₉ hZ_bit₉ hX_bits₉ with
    ⟨s₁₀, t₁₀, i_r, v_r, VA_r, VB_r, hex₁₀, ht₁₀, hv_in_r, hsep_r, _, _, _,
      _, _, _, _, _, hr25_10, _, _, hZ_bit₁₀, _, harr₁₀, hreg₁₀⟩
  change t₁₀ ≤ 12 + p * (100 + 165 * (n' + 1) + 2 * m_H + 84 * m_H +
    (ξ + 1) * (65 + 264 * (n' + 1) + 62 * m_H)) at ht₁₀
  have hG_arr₁₀ : s₁₀.arrs 17 = G_r.enc ++ [] := by
    rw [harr₁₀ 17 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), List.append_nil]
    exact hG_arr₇
  have hZ_arr₁₀ : s₁₀.arrs 9 = bitSetList Z_r := hZ_bit₁₀.arr_eq_bitSetList
  have hemb_arr₁₀ : s₁₀.arrs 16 = List.ofFn (fun u : Fin (n' + 1) => (emb_r u).1) := by
    rw [harr₁₀ 16 (Or.inr (Or.inr (Or.inl rfl)))]
    change s₇.arrs 16 = _
    rw [harr₇ 16 (by omega)]
    exact hemb_arr₅
  -- 4f. Delete `v_r` from `G_r` (`deleteVertexMultiDigraphProg 17 2 (18 + p) 25 26`)
  have hedges_del_w : (G_r.deleteVertex v_r).numEdges < 2 ^ w :=
    Nat.lt_of_le_of_lt (Alg65Trace.numEdges_deleteVertex_le G_r v_r) hedges_r_w
  rcases deleteVertexMultiDigraphProg_exec G_r v_r [] 17 2 (18 + p) 25 26
      (by decide) (by omega) (by decide) hw3 hnr_w hm3_w hedges_del_w
      hG_arr₁₀ hr25_10 with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hG_arr₁₁, hr26_11, hr27_11, hr28_11, harr₁₁, hreg₁₁⟩
  -- 4g. Delete `v_r` from `Z_r` (`deleteNthArrProg 9 2 26 25 29` + `readSliceProg`)
  have hr25_11 : s₁₁.regs 25 = v_r.1 := by
    rw [hreg₁₁ 25 (by decide)]; exact hr25_10
  have hZ_arr₁₁ : s₁₁.arrs 9 = List.ofFn (fun u : Fin (n' + 1) => if u ∈ Z_r then 1 else 0) := by
    rw [harr₁₁ 9 (by decide) (by omega)]; exact hZ_arr₁₀
  rcases deleteNthArrProg_exec (fun u : Fin (n' + 1) => if u ∈ Z_r then 1 else 0) v_r
      9 2 26 25 29 (by decide) (by decide) (by decide) hw hnr_w
      (fun u => by split_ifs <;> omega) hZ_arr₁₁ hr26_11 hr25_11 with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hZ_arr₁₂, harr₁₂, hreg₁₂⟩
  rw [← bitSetList_deleteVertexFinset Z_r v_r] at hZ_arr₁₂
  have hZ_next_w : ∀ b ∈ bitSetList (deleteVertexFinset Z_r v_r), b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one (deleteVertexFinset Z_r v_r) idx hidx
    omega
  rcases copyListProg_exec 9 (18 + p + 1) 26 29 (by omega) (by decide)
      (bitSetList (deleteVertexFinset Z_r v_r)) (length_bitSetList _) hZ_next_w hw hn'_w
      hZ_arr₁₂ (by rw [hreg₁₂ 26 (by decide)]; exact hr26_11) with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hZ_arr₁₃, harr₁₃, hreg₁₃⟩
  -- 4h. Delete `v_r` from `emb_r` (`deleteNthArrProg 16 2 26 25 29` + `readSliceProg`)
  have hemb_arr₁₃ : s₁₃.arrs 16 = List.ofFn (fun u : Fin (n' + 1) => (emb_r u).1) := by
    rw [harr₁₃ 16 (by omega), harr₁₂ 16 (by decide) (by decide),
      harr₁₁ 16 (by decide) (by omega)]
    exact hemb_arr₁₀
  have hr26_13 : s₁₃.regs 26 = n' := by
    rw [hreg₁₃ 26 (by decide), hreg₁₂ 26 (by decide)]; exact hr26_11
  have hr25_13 : s₁₃.regs 25 = v_r.1 := by
    rw [hreg₁₃ 25 (by decide), hreg₁₂ 25 (by decide)]; exact hr25_11
  rcases deleteNthArrProg_exec (fun u : Fin (n' + 1) => (emb_r u).1) v_r
      16 2 26 25 29 (by decide) (by decide) (by decide) hw hnr_w
      (fun u => Nat.lt_trans (emb_r u).2 hn0_w) hemb_arr₁₃ hr26_13 hr25_13 with
    ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hemb_arr₁₄, harr₁₄, hreg₁₄⟩
  have hemb_next_w : ∀ b ∈ List.ofFn ((fun u : Fin (n' + 1) => (emb_r u).1) ∘ v_r.succAbove), b < 2 ^ w := by
    intro b hb
    rw [List.mem_ofFn] at hb
    rcases hb with ⟨u, rfl⟩
    exact Nat.lt_trans (emb_r (v_r.succAbove u)).2 hn0_w
  rcases copyListProg_exec 16 (18 + p + 2) 26 29 (by omega) (by decide)
      (List.ofFn ((fun u : Fin (n' + 1) => (emb_r u).1) ∘ v_r.succAbove)) (by simp)
      hemb_next_w hw hn'_w hemb_arr₁₄
      (by rw [hreg₁₄ 26 (by decide)]; exact hr26_13) with
    ⟨s₁₅, t₁₅, hex₁₅, ht₁₅, hemb_arr₁₅, harr₁₅, hreg₁₅⟩
  -- 5. Assemble the updated `Alg65LoopState` and step-count bound
  have htr_next :
      Alg65Trace ξ δ (x.G.cap δ) x.Z
        (G_r.deleteVertex v_r) (deleteVertexFinset Z_r v_r) (emb_r ∘ v_r.succAbove) :=
    .step X_r i_r v_r VA_r VB_r hst.trace hgt hmodel_r hv_in_r hsep_r
  have hst_next :
      Alg65LoopState ξ δ x n'
        (G_r.deleteVertex v_r) (deleteVertexFinset Z_r v_r) (emb_r ∘ v_r.succAbove) s₁₅ := by
    refine ⟨htr_next, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [harr₁₅ (18 + p) (by omega), harr₁₄ (18 + p) (by omega) (by omega),
        harr₁₃ (18 + p) (by omega), harr₁₂ (18 + p) (by omega) (by omega)]
      exact hG_arr₁₁
    · rw [harr₁₅ (18 + p + 1) (by omega), harr₁₄ (18 + p + 1) (by omega) (by omega)]
      exact hZ_arr₁₃
    · exact hemb_arr₁₅
    · rw [hreg₁₅ 26 (by decide), hreg₁₄ 26 (by decide)]; exact hr26_13
    · rw [hreg₁₅ 27 (by decide), hreg₁₄ 27 (by decide), hreg₁₃ 27 (by decide), hreg₁₂ 27 (by decide)]
      exact hr27_11
    · rw [hreg₁₅ 28 (by decide), hreg₁₄ 28 (by decide), hreg₁₃ 28 (by decide), hreg₁₂ 28 (by decide)]
      exact hr28_11
  have htime_bound :
      t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (6 + (t₇ + (2 + (4 + (t₁₀ + (t₁₁ + (t₁₂ + (t₁₃ + (t₁₄ + t₁₅))))))))))))) ≤
        alg65IterConst ξ δ * (x.n + 1) ^ 2 := by
    let S2 := (x.n + 1) ^ 2
    have hS2_eq : S2 = (x.n + 1) * (x.n + 1) := Nat.pow_two (x.n + 1)
    have hS2_expand : S2 = x.n * x.n + 2 * x.n + 1 := by
      rw [hS2_eq, Nat.add_mul, Nat.mul_add]; omega
    have h1_S2 : 1 ≤ S2 := by omega
    have hnr_S2 : n' + 1 ≤ S2 := by omega
    have hm'_S2 : G_r.numActivePairs ≤ S2 := by omega
    have hmH_S2 : m_H ≤ S2 := by omega
    have hsq_le : (n' + 1 + 1) ^ 2 ≤ S2 := Nat.pow_le_pow_left (by omega) 2
    have ht₂_S2 : t₂ ≤ alg64StepConst p * S2 :=
      le_trans ht₂ (Nat.mul_le_mul_left (alg64StepConst p) hsq_le)
    have h10_inner :
        100 + 165 * (n' + 1) + 2 * m_H + 84 * m_H +
          (ξ + 1) * (65 + 264 * (n' + 1) + 62 * m_H) ≤
          (ξ + 1) * (800 * S2) := by
      have h_a : 100 + 165 * (n' + 1) + 2 * m_H + 84 * m_H ≤ 1 * (351 * S2) := by
        have := h1_S2; have := hnr_S2; have := hmH_S2
        omega
      have h_b : 1 * (351 * S2) ≤ (ξ + 1) * (351 * S2) :=
        Nat.mul_le_mul_right _ (by omega)
      have h_c : 65 + 264 * (n' + 1) + 62 * m_H ≤ 391 * S2 := by
        have := h1_S2; have := hnr_S2; have := hmH_S2
        omega
      have h_d : (ξ + 1) * (65 + 264 * (n' + 1) + 62 * m_H) ≤ (ξ + 1) * (391 * S2) :=
        Nat.mul_le_mul_left (ξ + 1) h_c
      have h_sum : (ξ + 1) * (351 * S2) + (ξ + 1) * (391 * S2) ≤
          (ξ + 1) * (800 * S2) := by
        rw [← Nat.left_distrib]
        exact Nat.mul_le_mul_left (ξ + 1) (by omega)
      exact le_trans (Nat.add_le_add (le_trans h_a h_b) h_d) h_sum
    have ht₁₀_S2 : t₁₀ ≤ 12 + p * (ξ + 1) * 800 * S2 := by
      have hp_mul :
          p * (100 + 165 * (n' + 1) + 2 * m_H + 84 * m_H +
            (ξ + 1) * (65 + 264 * (n' + 1) + 62 * m_H)) ≤
            p * ((ξ + 1) * (800 * S2)) :=
        Nat.mul_le_mul_left p h10_inner
      have hp_assoc : p * ((ξ + 1) * (800 * S2)) = p * (ξ + 1) * 800 * S2 := by
        simp [Nat.mul_assoc]
      rw [hp_assoc] at hp_mul
      exact le_trans ht₁₀ (Nat.add_le_add_left hp_mul 12)
    have hrest_S2 :
        t₁ + t₃ + t₄ + t₅ + 6 + t₇ + 2 + 4 + 12 + t₁₁ + t₁₂ + t₁₃ + t₁₄ + t₁₅ ≤
          1200 * S2 := by
      clear ht₂ ht₂_S2 ht₁₀ ht₁₀_S2 h10_inner hpow_r_w hpow_64_w
      omega
    have hiter_expand :
        alg65IterConst ξ δ * S2 =
          1200 * S2 + alg64StepConst p * S2 + p * (ξ + 1) * 800 * S2 := by
      dsimp [alg65IterConst]
      change (1200 + alg64StepConst p + p * (ξ + 1) * 800) * S2 = _
      rw [Nat.add_mul, Nat.add_mul]
    change _ ≤ alg65IterConst ξ δ * S2
    rw [hiter_expand]
    generalize alg64StepConst p * S2 = M64 at ht₂_S2 ⊢
    generalize p * (ξ + 1) * 800 * S2 = M62 at ht₁₀_S2 ⊢
    generalize 1200 * S2 = M1200 at hrest_S2 ⊢
    clear ht₁ ht₂ ht₃ ht₄ ht₅ ht₇ ht₁₀ ht₁₁ ht₁₂ ht₁₃ ht₁₄ ht₁₅
      h10_inner hpow_r_w hpow_64_w
    omega
  exact ⟨G_r.deleteVertex v_r, deleteVertexFinset Z_r v_r, emb_r ∘ v_r.succAbove, s₁₅, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁
        (.seq hex₁₂ (.seq hex₁₃ (.seq hex₁₄ hex₁₅))))))))))))),
    htime_bound, hst_next⟩

theorem eval_alg65LoopCond {w : ℕ} (ξ δ n_r e_r : ℕ) (s : State)
    (hr26 : s.regs 26 = n_r) (hr28 : s.regs 28 = e_r)
    (hw : 1 < 2 ^ w) (hC_w : alg65Const ξ δ < 2 ^ w)
    (hn_w : n_r < 2 ^ w) (hCn_w : alg65Const ξ δ * n_r < 2 ^ w)
    (he_w : e_r < 2 ^ w) :
    Expr.eval w s (.op .lt (.op .mul (.const (alg65Const ξ δ)) (.reg 26)) (.reg 28)) =
      some (if alg65Const ξ δ * n_r < e_r then 1 else 0) := by
  have h0_w : 0 < 2 ^ w := by omega
  simp only [Expr.eval, hr26, hr28, checkWord_of_lt hC_w, checkWord_of_lt hn_w,
    checkWord_of_lt he_w, BinOp.eval, BinOp.raw, checkWord_of_lt hCn_w]
  split_ifs <;> simp [checkWord_of_lt hw, checkWord_of_lt h0_w]

/-- Correctness of the main `.while` loop `alg65LoopProg ξ δ`: starting from any state
satisfying `Alg65LoopState ξ δ x n_r G_r Z_r emb_r s`, it terminates in a state `s'`
and subdigraph `(n', G', Z', emb')` with `|E(G')| ≤ alg65Const ξ δ * |V(G')|` and a valid
deletion trace `Alg65Trace ξ δ (x.G.cap δ) x.Z G' Z' emb'`. -/
theorem alg65Loop_exec {w : ℕ} (ξ δ : ℕ) (x : Alg65Input ξ δ)
    (hw3 : 3 < 2 ^ w)
    (hn0_w : x.n < 2 ^ w)
    (h2n0_w : 2 * x.n < 2 ^ w)
    (hp_w : alg62Param ξ δ < 2 ^ w)
    (hC_n_w : alg65Const ξ δ < 2 ^ w ∧ alg65Const ξ δ * x.n < 2 ^ w)
    (hm3_cap_w : 2 + 3 * (x.G.cap δ).numActivePairs < 2 ^ w)
    (hedges_cap_w : (x.G.cap δ).numEdges < 2 ^ w)
    (hpow_64_w : (x.n + 2) ^ (alg62Param ξ δ + 2) < 2 ^ w)
    (n_r : ℕ) (G_r : MultiDigraph n_r) (Z_r : Finset (Fin n_r))
    (emb_r : Fin n_r → Fin x.n)
    {s : State}
    (hst : Alg65LoopState ξ δ x n_r G_r Z_r emb_r s) :
    ∃ (n' : ℕ) (G' : MultiDigraph n') (Z' : Finset (Fin n'))
      (emb' : Fin n' → Fin x.n) (s' : State) (t : ℕ),
      Exec w (alg65LoopProg ξ δ) s s' t ∧
      t ≤ 5 + n_r * (5 + alg65IterConst ξ δ * (x.n + 1) ^ 2) ∧
      G'.numEdges ≤ alg65Const ξ δ * n' ∧
      Alg65LoopState ξ δ x n' G' Z' emb' s' := by
  have hw : 1 < 2 ^ w := by omega
  induction n_r generalizing s with
  | zero =>
    have hedges_zero : G_r.numEdges = 0 := by simp [MultiDigraph.numEdges]
    have hnr_w : (0 : ℕ) < 2 ^ w := by omega
    have hCn_r_w : alg65Const ξ δ * 0 < 2 ^ w := by omega
    have hcond :
        Expr.eval w s (.op .lt (.op .mul (.const (alg65Const ξ δ)) (.reg 26)) (.reg 28)) =
          some 0 := by
      rw [eval_alg65LoopCond ξ δ 0 0 s hst.hr26 (by rw [hst.hr28, hedges_zero])
        hw hC_n_w.1 hnr_w hCn_r_w hnr_w]
      simp
    exact ⟨0, G_r, Z_r, emb_r, s, 5, .while_false hcond, by omega, by omega, hst⟩
  | succ n' ih =>
    have hnr_le : n' + 1 ≤ x.n := hst.trace.le_num_vertices
    have hnr_w : n' + 1 < 2 ^ w := by omega
    have hCn_r_le : alg65Const ξ δ * (n' + 1) ≤ alg65Const ξ δ * x.n :=
      Nat.mul_le_mul_left (alg65Const ξ δ) hnr_le
    have hCn_r_w : alg65Const ξ δ * (n' + 1) < 2 ^ w :=
      Nat.lt_of_le_of_lt hCn_r_le hC_n_w.2
    have hedges_r_le : G_r.numEdges ≤ (x.G.cap δ).numEdges := hst.trace.numEdges_le
    have hedges_r_w : G_r.numEdges < 2 ^ w :=
      Nat.lt_of_le_of_lt hedges_r_le hedges_cap_w
    by_cases hgt : alg65Const ξ δ * (n' + 1) < G_r.numEdges
    · have hcond :
          Expr.eval w s (.op .lt (.op .mul (.const (alg65Const ξ δ)) (.reg 26)) (.reg 28)) =
            some 1 := by
        rw [eval_alg65LoopCond ξ δ (n' + 1) G_r.numEdges s hst.hr26 hst.hr28
          hw hC_n_w.1 hnr_w hCn_r_w hedges_r_w]
        simp [hgt]
      rcases alg65LoopBody_exec ξ δ x n' G_r Z_r emb_r hw3 hn0_w h2n0_w hp_w
          hm3_cap_w hedges_cap_w hpow_64_w hgt hst with
        ⟨G_next, Z_next, emb_next, s₁, t₁, hex₁, ht₁, hst₁⟩
      rcases ih G_next Z_next emb_next hst₁ with
        ⟨n_out, G_out, Z_out, emb_out, s_out, t_out, hex_out, ht_out, hedges_out, hst_out⟩
      refine ⟨n_out, G_out, Z_out, emb_out, s_out, 5 + t₁ + t_out,
        .while_true hcond (by omega) hex₁ hex_out, ?_, hedges_out, hst_out⟩
      generalize alg65IterConst ξ δ * (x.n + 1) ^ 2 = M at ht₁ ht_out ⊢
      have hmul_succ : (n' + 1) * (5 + M) = (5 + M) + n' * (5 + M) := by
        rw [Nat.add_comm n' 1, Nat.add_mul, Nat.one_mul]
      omega
    · have hcond :
          Expr.eval w s (.op .lt (.op .mul (.const (alg65Const ξ δ)) (.reg 26)) (.reg 28)) =
            some 0 := by
        rw [eval_alg65LoopCond ξ δ (n' + 1) G_r.numEdges s hst.hr26 hst.hr28
          hw hC_n_w.1 hnr_w hCn_r_w hedges_r_w]
        simp [hgt]
      exact ⟨n' + 1, G_r, Z_r, emb_r, s, 5,
        .while_false hcond, by omega, Nat.le_of_not_lt hgt, hst⟩

/-! ### Section 4: Output Decoding and End-to-End Theorem `gm13_algorithm_6_5` -/

/-- Pure lookup of the multiplicity of pair `(u, v)` in `k` consecutive triples
`x₀, y₀, m₀, …` of a flat word list. -/
def lookupTripleMult (u v : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | k + 1, x :: y :: m :: rest =>
    if u = x ∧ v = y then m else lookupTripleMult u v k rest
  | _ + 1, _ => 0

theorem lookupTripleMult_flatTriples {n : ℕ} (G : MultiDigraph n)
    (u v : Fin n) :
    ∀ (L : List (Fin n × Fin n)) (extra : List ℕ),
      L.Pairwise (· ≠ ·) →
      lookupTripleMult u.1 v.1 L.length (G.flatTriples L ++ extra) =
        if (u, v) ∈ L then G.edgeMult u v else 0
  | [], extra, _ => by simp [lookupTripleMult, MultiDigraph.flatTriples]
  | (a, b) :: rest, extra, hpw => by
    rw [List.pairwise_cons] at hpw
    simp only [List.length_cons, MultiDigraph.flatTriples, List.cons_append,
      lookupTripleMult, List.mem_cons, Prod.mk.injEq, Fin.ext_iff]
    by_cases huv : u.1 = a.1 ∧ v.1 = b.1
    · have hu : a = u := Fin.ext huv.1.symm
      have hv : b = v := Fin.ext huv.2.symm
      subst hu hv
      simp
    · simp only [huv, ite_false, false_or]
      exact lookupTripleMult_flatTriples G u v rest extra hpw.2

theorem lookupTripleMult_activePairsList {n : ℕ} (G : MultiDigraph n)
    (u v : Fin n) (extra : List ℕ) :
    lookupTripleMult u.1 v.1 G.numActivePairs (G.flatTriples G.activePairsList ++ extra) =
      G.edgeMult u v := by
  unfold MultiDigraph.numActivePairs
  rw [lookupTripleMult_flatTriples G u v G.activePairsList extra G.nodup_activePairsList]
  simp only [MultiDigraph.mem_activePairsList]
  by_cases hpos : 0 < G.edgeMult u v
  · simp [hpos]
  · simp [hpos]
    omega

/-- Output of GM XIII Algorithm (6.5) on an input multi-digraph with `n₀` vertices:
a subdigraph `G' : MultiDigraph n'` together with an embedding `emb : Fin n' → Fin n₀`
into the original vertex set `Fin n₀`. -/
structure Alg65Output (n₀ : ℕ) where
  /-- Number of vertices `|V(G')|` of the output subdigraph. -/
  n' : ℕ
  /-- Output multi-digraph `G'`. -/
  G' : MultiDigraph n'
  /-- Vertex embedding `V(G') → V(G)` into the input multi-digraph. -/
  emb : Fin n' → Fin n₀

theorem Alg65Output.ext {n₀ : ℕ} {A B : Alg65Output n₀}
    (hn : A.n' = B.n')
    (hG : ∀ u v : Fin A.n',
      A.G'.edgeMult u v = B.G'.edgeMult (u.cast hn) (v.cast hn))
    (hemb : ∀ u : Fin A.n', A.emb u = B.emb (u.cast hn)) :
    A = B := by
  cases A with | mk nA GA embA =>
  cases B with | mk nB GB embB =>
  dsimp only at hn hG hemb
  subst hn
  congr
  · ext u v; exact hG u v
  · funext u; exact hemb u

/-- Decoded vertex count `n'` from `outArr`, safeguarded to `0` when `n₀ = 0`. -/
def decAlg65N (n₀ : ℕ) (out : List ℕ) : ℕ :=
  if n₀ = 0 then 0 else out.getD 0 0

/-- Pure decoder reconstructing `Alg65Output n₀` from `outArr = G'.enc ++ emb_list`. -/
def decAlg65Out (n₀ : ℕ) (out : List ℕ) : Alg65Output n₀ where
  n' := decAlg65N n₀ out
  G' := {
    edgeMult := fun u v =>
      lookupTripleMult u.1 v.1 (out.getD 1 0) (out.drop 2)
  }
  emb := fun u =>
    have hn₀ : 0 < n₀ := by
      by_contra h
      have h0 : n₀ = 0 := by omega
      have hu := u.2
      simp [decAlg65N, h0] at hu
    ⟨(out.getD (2 + 3 * out.getD 1 0 + u.1) 0) % n₀, Nat.mod_lt _ hn₀⟩

theorem decAlg65Out_eq {n₀ n' : ℕ} (G' : MultiDigraph n') (emb : Fin n' → Fin n₀)
    (hle : n' ≤ n₀) :
    decAlg65Out n₀ (G'.enc ++ List.ofFn (fun u : Fin n' => (emb u).1)) =
      ⟨n', G', emb⟩ := by
  let out := G'.enc ++ List.ofFn (fun u : Fin n' => (emb u).1)
  have hn' : decAlg65N n₀ out = n' := by
    unfold decAlg65N
    split_ifs with h0
    · omega
    · simp [out, MultiDigraph.enc]
  have hm' : out.getD 1 0 = G'.numActivePairs := by
    simp [out, MultiDigraph.enc, MultiDigraph.numActivePairs]
  have hdrop : out.drop 2 =
      G'.flatTriples G'.activePairsList ++ List.ofFn (fun u : Fin n' => (emb u).1) := by
    simp [out, MultiDigraph.enc]
  apply Alg65Output.ext hn'
  · intro u v
    dsimp [decAlg65Out]
    rw [hm', hdrop]
    have hu : u.1 = (u.cast hn').1 := rfl
    have hv : v.1 = (v.cast hn').1 := rfl
    rw [hu, hv, lookupTripleMult_activePairsList]
  · intro u
    apply Fin.ext
    dsimp [decAlg65Out]
    rw [hm']
    have hlen_enc : G'.enc.length = 2 + 3 * G'.numActivePairs := G'.length_enc
    have hu_lt : u.1 < n' := (u.cast hn').2
    have hget : out.getD (2 + 3 * G'.numActivePairs + u.1) 0 = (emb (u.cast hn')).1 := by
      dsimp [out]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega)]
      have hsub : 2 + 3 * G'.numActivePairs + u.1 - G'.enc.length = (u.cast hn').1 := by
        change 2 + 3 * G'.numActivePairs + u.1 - G'.enc.length = u.1
        omega
      rw [hsub, List.getElem?_ofFn]
      simp [(u.cast hn').2]
    rw [hget, Nat.mod_eq_of_lt (emb (u.cast hn')).2]

/-- Mathematical validity predicate for the output `(n', G', emb)` of GM XIII Algorithm (6.5)
on input `x : Alg65Input ξ δ`:
1. `emb : Fin n' → Fin x.n` is injective (identifying `V(G')` with a subset of `V(G)`).
2. `G'` is a subdigraph of `x.G` via `emb`: for all `u, v : Fin n'`,
   `G'.edgeMult u v ≤ x.G.edgeMult (emb u) (emb v)`, and
   `(G'.toEmbeddedGMDigraph emb).IsSubdigraph x.G.toGMDigraph`.
3. `Z ⊆ V(G')` via `emb`: `x.Z ⊆ Finset.univ.image emb` and
   `x.Z.toNatSet ⊆ (G'.toEmbeddedGMDigraph emb).vertexSet`.
4. `|E(G')| ≤ alg65Const ξ δ * |V(G')|`, where
   `alg65Const ξ δ = δ + 2 * (δ + 1) * 2 ^ (alg62Param ξ δ - 3)`, both on `MultiDigraph`
   (`G'.numEdges ≤ alg65Const ξ δ * n'`) and on `GM13.Digraph`
   (`(G'.toEmbeddedGMDigraph emb).edgeSet.ncard ≤ alg65Const ξ δ * (G'.toEmbeddedGMDigraph emb).vertexSet.ncard`).
5. `x.G` and `G'` have the same `δ`-folio relative to `x.Z`, both in `GM13.HasSameDeltaFolioRel`
   and in `dp`'s `IsDeltaFolioRep` representation (`FolioStatement.lean`), witnessed by a valid
   step-by-step deletion trace `Alg65Trace ξ δ (x.G.cap δ) x.Z G' Z' emb`. -/
def IsValidAlg65Output (ξ δ : ℕ) (x : Alg65Input ξ δ) (out : Alg65Output x.n) : Prop :=
  Function.Injective out.emb ∧
  (∀ u v : Fin out.n', out.G'.edgeMult u v ≤ x.G.edgeMult (out.emb u) (out.emb v)) ∧
  x.Z ⊆ Finset.univ.image out.emb ∧
  out.G'.numEdges ≤ alg65Const ξ δ * out.n' ∧
  (out.G'.toEmbeddedGMDigraph out.emb).IsSubdigraph x.G.toGMDigraph ∧
  x.Z.toNatSet ⊆ (out.G'.toEmbeddedGMDigraph out.emb).vertexSet ∧
  GM13.HasSameDeltaFolioRel x.G.toGMDigraph (out.G'.toEmbeddedGMDigraph out.emb) δ x.Z.toNatSet ∧
  (out.G'.toEmbeddedGMDigraph out.emb).edgeSet.ncard ≤
    alg65Const ξ δ * (out.G'.toEmbeddedGMDigraph out.emb).vertexSet.ncard ∧
  ∃ Z' : Finset (Fin out.n'),
    Z'.image out.emb = x.Z ∧
    ∃ (hcard : Z'.card = x.Z.card),
      (∀ F : FolioSetRep x.Z.card δ,
        IsDeltaFolioRep δ x.G x.Z F ↔
          IsDeltaFolioRep δ out.G' Z' (F.castCard hcard.symm)) ∧
      Alg65Trace ξ δ (x.G.cap δ) x.Z out.G' Z' out.emb

/-- Complete Word RAM program for GM XIII Algorithm (6.5) with fixed parameters `ξ, δ : ℕ`:
1. Reads `n = |V(G)|` and `m = numActivePairs` from `inArr[0..1]`, and initializes `emb_0 = id`
   in array `18 + p + 2` (`initIdArrProg`).
2. Computes the offset `2 + 3 * m` of `bitSetList Z` in `inArr` and copies `bitSetList Z` into
   array `18 + p + 1` (`readSliceProg`).
3. Runs Step (1) (`capMultiDigraphProg δ inArr 2 (18 + p) 26`) to build `H = G.cap δ` in
   array `18 + p`, with `r_26 = n`, `r_27 = H.numActivePairs`, and `r_28 = H.numEdges`.
4. Runs the recursion loop `alg65LoopProg ξ δ` (Steps (2)–(4)).
5. Writes `G'.enc ++ emb'` to `outArr` (`alg65WriteOutProg p`). -/
def alg65EndToEndProg (ξ δ : ℕ) : Cmd :=
  let p := alg62Param ξ δ
  .seq (.assign 26 (.read inArr (.const 0)))
    (.seq (initIdArrProg (18 + p + 2) 26 29)
      (.seq (.assign 27 (.read inArr (.const 1)))
        (.seq (.assign 29 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27))))
          (.seq (readSliceProg inArr (.reg 29) (18 + p + 1) (.reg 26) 30)
            (.seq (capMultiDigraphProg δ inArr 2 (18 + p) 26)
              (.seq (alg65LoopProg ξ δ)
                (alg65WriteOutProg p)))))))

theorem numEdges_le_of_edgeMult_le {n : ℕ} (G : MultiDigraph n) (c : ℕ)
    (h : ∀ u v : Fin n, G.edgeMult u v ≤ c) :
    G.numEdges ≤ c * (n * n) := by
  calc G.numEdges
    _ = ∑ u : Fin n, ∑ v : Fin n, G.edgeMult u v := rfl
    _ ≤ ∑ _u : Fin n, ∑ _v : Fin n, c :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h u v
    _ = c * (n * n) := by simp [Nat.mul_comm, Nat.mul_left_comm]

/-- **GM XIII Algorithm (6.5)** (Robertson–Seymour, page 85 / page 87):
For fixed `ξ, δ : ℕ`, with `p = ⌊5ξ/2⌋ + 3δ + 1` (`alg62Param ξ δ`) and
`C = δ + 2(δ + 1)2^{p - 3}` (`alg65Const ξ δ`), there is a Word RAM program
`alg65EndToEndProg ξ δ` with running time `O(v³)` (`T(v) = (v + 1)³` with `v = |V(G)|`)
that takes any multi-digraph `G` and `Z ⊆ V(G)` with `|Z| ≤ ξ` and outputs a subdigraph `G'`
of `G` with `Z ⊆ V(G')` and `|E(G')| ≤ C |V(G')|` together with a valid Algorithm (6.5)
vertex-deletion trace from `G.cap δ` to `G'`. -/
theorem gm13_algorithm_6_5 (ξ δ : ℕ) :
    ComputesArrRelInTime (alg65Size (ξ := ξ) (δ := δ)) (encAlg65In (ξ := ξ) (δ := δ))
      (fun x out => IsValidAlg65Output ξ δ x (decAlg65Out x.n out))
      (alg65EndToEndProg ξ δ) (fun s => (s + 1) ^ 3) := by
  unfold ComputesArrRelInTime ComputesRelInTime
  let p := alg62Param ξ δ
  let C_alg := alg65Const ξ δ
  let K_iter := alg65IterConst ξ δ
  have hp_pos : 1 ≤ p := by dsimp [p, alg62Param]; omega
  refine ⟨450 + K_iter, 2 * p + 4, by omega, by omega,
    fun x s₀ hs₀ => ?_⟩
  set w := wordSize (2 * p + 4) (alg65Size x)
  -- Word size bounds from `w = wordSize (2 * p + 4) x.n`
  have hpow_full : (x.n + 2) ^ (2 * p + 4) < 2 ^ w :=
    pow_lt_two_pow_wordSize (c := 2 * p + 4) (by omega) x.n
  have h2_le_base : 2 ≤ x.n + 2 := by omega
  have h2_pow_lt : 2 ^ (2 * p + 4) ≤ (x.n + 2) ^ (2 * p + 4) :=
    Nat.pow_le_pow_left h2_le_base (2 * p + 4)
  have hw6 : 64 ≤ 2 ^ w := by
    have h6 : 6 ≤ 2 * p + 4 := by omega
    have h64 : 64 = 2 ^ 6 := by decide
    rw [h64]
    exact le_trans (Nat.pow_le_pow_right (by omega) h6)
      (le_trans h2_pow_lt (Nat.le_of_lt hpow_full))
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hpow_le : ∀ j ≤ 2 * p + 4, (x.n + 2) ^ j < 2 ^ w := by
    intro j hj
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hj) hpow_full
  have hpow1 : x.n + 2 < 2 ^ w := by simpa using hpow_le 1 (by omega)
  have hpow2 : (x.n + 2) ^ 2 < 2 ^ w := hpow_le 2 (by omega)
  have hpow_64_w : (x.n + 2) ^ (p + 2) < 2 ^ w := hpow_le (p + 2) (by omega)
  have hm_sq : x.G.numActivePairs ≤ x.n * x.n := x.G.numActivePairs_le_sq
  have h8sq_w : 8 * (x.n * x.n) + 32 * x.n + 32 < 2 ^ w := by
    have h1 : 8 ≤ (x.n + 2) ^ 3 := by
      have h8 : 8 = 2 ^ 3 := by decide
      rw [h8]
      exact Nat.pow_le_pow_left h2_le_base 3
    have h2 : 8 * (x.n + 2) ^ 2 ≤ (x.n + 2) ^ 3 * (x.n + 2) ^ 2 :=
      Nat.mul_le_mul_right _ h1
    have h3 : (x.n + 2) ^ 3 * (x.n + 2) ^ 2 = (x.n + 2) ^ 5 := by
      rw [← Nat.pow_add]
    have h4 : 8 * (x.n * x.n) + 32 * x.n + 32 = 8 * (x.n + 2) ^ 2 := by
      rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    have h5 : (x.n + 2) ^ 5 < 2 ^ w := hpow_le 5 (by omega)
    omega
  have hn0_w : x.n < 2 ^ w := by omega
  have h2n0_w : 2 * x.n < 2 ^ w := by omega
  have hm3_in_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hm3_plus_n_w : 2 + 3 * x.G.numActivePairs + x.n < 2 ^ w := by omega
  have h2len_out_w : 2 * (2 + 3 * x.G.numActivePairs + x.n) < 2 ^ w := by omega
  have hcap_le_G : (x.G.cap δ).numActivePairs ≤ x.G.numActivePairs := by
    simp only [MultiDigraph.numActivePairs, MultiDigraph.activePairsList_cap]
    exact List.length_filter_le _ _
  have hm3_cap_w : 2 + 3 * (x.G.cap δ).numActivePairs < 2 ^ w := by omega
  have hδ1_le_2p : δ + 1 ≤ 2 ^ p := by
    have hδ_lt_p : δ < p := by dsimp [p, alg62Param]; omega
    have h1 : δ + 1 ≤ p := hδ_lt_p
    exact le_trans h1 (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hδ_w : δ + 1 < 2 ^ w := by
    have h1 : 2 ^ p ≤ (x.n + 2) ^ p := Nat.pow_le_pow_left h2_le_base p
    have h2 : (x.n + 2) ^ p < 2 ^ w := hpow_le p (by omega)
    omega
  have hedges_cap_le : (x.G.cap δ).numEdges ≤ (δ + 1) * (x.n * x.n) :=
    numEdges_le_of_edgeMult_le (x.G.cap δ) (δ + 1) (x.G.cap_edgeMult_le_succ δ)
  have hedges_cap_w : (x.G.cap δ).numEdges < 2 ^ w := by
    have h1 : (δ + 1) * (x.n * x.n) ≤ 2 ^ p * (x.n + 2) ^ 2 := by
      refine Nat.mul_le_mul hδ1_le_2p ?_
      rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    have h2 : 2 ^ p * (x.n + 2) ^ 2 ≤ (x.n + 2) ^ p * (x.n + 2) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2_le_base p)
    rw [← Nat.pow_add] at h2
    exact Nat.lt_of_le_of_lt (le_trans hedges_cap_le (le_trans h1 h2)) hpow_64_w
  have hp_w : p < 2 ^ w := by
    have h1 : p < 2 ^ p := Nat.lt_two_pow_self
    have h2 : 2 ^ p ≤ (x.n + 2) ^ p := Nat.pow_le_pow_left h2_le_base p
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 h2) (Nat.le_of_lt (hpow_le p (by omega)))
  have hC_le_pow : C_alg ≤ 2 ^ (2 * p + 2) := by
    change δ + 2 * (δ + 1) * 2 ^ (p - 3) ≤ 2 ^ (2 * p + 2)
    have h1 : 2 ^ (p - 3) ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 * (δ + 1) * 2 ^ (p - 3) ≤ 2 * 2 ^ p * 2 ^ p :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hδ1_le_2p) h1
    have h3 : 2 ^ p + 2 * 2 ^ p * 2 ^ p ≤ 2 ^ (2 * p + 2) := by
      have h4 : 2 * 2 ^ p * 2 ^ p = 2 * 2 ^ (2 * p) := by
        rw [Nat.mul_assoc, ← Nat.pow_add, ← Nat.two_mul]
      have h5 : 2 ^ p ≤ 2 ^ (2 * p) := Nat.pow_le_pow_right (by omega) (by omega)
      have h6 : 2 ^ (2 * p + 2) = 4 * 2 ^ (2 * p) := by
        rw [Nat.pow_add, Nat.mul_comm]
      omega
    exact le_trans (Nat.add_le_add (by omega : δ ≤ 2 ^ p) h2) h3
  have hC_n_w : C_alg < 2 ^ w ∧ C_alg * x.n < 2 ^ w := by
    have h1 : C_alg * (x.n + 2) ≤ (x.n + 2) ^ (2 * p + 2) * (x.n + 2) :=
      Nat.mul_le_mul_right (x.n + 2)
        (le_trans hC_le_pow (Nat.pow_le_pow_left h2_le_base (2 * p + 2)))
    have h2 : (x.n + 2) ^ (2 * p + 2) * (x.n + 2) = (x.n + 2) ^ (2 * p + 3) := by
      rw [← Nat.pow_succ]
    have h3 : (x.n + 2) ^ (2 * p + 3) < 2 ^ w := hpow_le (2 * p + 3) (by omega)
    have h4 : C_alg ≤ C_alg * (x.n + 2) := Nat.le_mul_of_pos_right _ (by omega)
    have h5 : C_alg * x.n ≤ C_alg * (x.n + 2) := Nat.mul_le_mul_left C_alg (by omega)
    omega
  -- Trace execution from `s₀` satisfying `hs₀ : s₀.arrs inArr = encAlg65In x`
  have hin₀ : s₀.arrs inArr = x.G.enc ++ bitSetList x.Z := hs₀
  -- 1. Read `r_26 := inArr[0]` and run `initIdArrProg (18 + p + 2) 26 29`
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero x.G _ hin₀
  let s₀' := s₀.setReg 26 x.n
  have hex₀' : Exec w (.assign 26 (.read inArr (.const 0))) s₀ s₀' 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn0_w])
  rcases initIdArrProg_exec (18 + p + 2) 26 29 (by decide) hw hn0_w
      (s := s₀') (by simp [s₀']) with
    ⟨s₁, t₁, hex₁, ht₁, hemb₁, harr₁, hreg₁⟩
  have hin₁ : s₁.arrs inArr = x.G.enc ++ bitSetList x.Z := by
    rw [harr₁ inArr (by dsimp [inArr]; omega)]; exact hin₀
  have hr26_1 : s₁.regs 26 = x.n := by
    rw [hreg₁ 26 (by decide)]; rfl
  -- 2. Read `m = x.G.numActivePairs` into `r_27` and set `r_29 := 2 + 3 * r_27`
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one x.G _ hin₁
  have hm_in_w : x.G.numActivePairs < 2 ^ w := by omega
  let s₂ := s₁.setReg 27 x.G.numActivePairs
  have hex₂ : Exec w (.assign 27 (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_len, h1_val, hm_in_w])
  let s₃ := s₂.setReg 29 (2 + 3 * x.G.numActivePairs)
  have hex₃ : Exec w (.assign 29 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27)))) s₂ s₃ 6 :=
    .assign (by simp [s₂, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hw3, hm_in_w, show 3 * x.G.numActivePairs < 2 ^ w by omega, hm3_in_w])
  -- 3. `readSliceProg inArr (.reg 29) (18 + p + 1) (.reg 26) 30`
  have hZ_w : ∀ b ∈ bitSetList x.Z, b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one x.Z idx hidx
    omega
  have hin₃ : s₃.arrs inArr = x.G.enc ++ bitSetList x.Z ++ [] := by
    change s₁.arrs inArr = _
    rw [List.append_nil]
    exact hin₁
  rcases readSliceProg_exec inArr (18 + p + 1) (.reg 29) 26 30
      (by dsimp [inArr]; omega) (by decide)
      x.G.enc (bitSetList x.Z) []
      x.G.length_enc (length_bitSetList x.Z) hZ_w hw hm3_plus_n_w
      (s := s₃)
      (by simp [s₃, Expr.eval, checkWord, hm3_in_w])
      hin₃
      (by change s₁.regs 26 = x.n; exact hr26_1) with
    ⟨s₄, t₄, hex₄, ht₄, hZ_arr₄, harr₄, hreg₄⟩
  dsimp [Expr.cost] at ht₄
  -- 4. `capMultiDigraphProg δ inArr 2 (18 + p) 26`
  have hin₄ : s₄.arrs inArr = x.G.enc ++ bitSetList x.Z := by
    rw [harr₄ inArr (by dsimp [inArr]; omega)]; exact hin₁
  rcases capMultiDigraphProg_exec x.G δ (bitSetList x.Z) inArr 2 (18 + p) 26
      (by dsimp [inArr]; omega) (by omega)
      hw3 hn0_w hδ_w hm3_in_w hedges_cap_w hin₄ with
    ⟨s₅, t₅, hex₅, ht₅, hG_arr₅, hr26_5, hr27_5, hr28_5, harr₅, _⟩
  -- 5. Build initial `Alg65LoopState` at `s₅` and run `alg65LoopProg ξ δ`
  have hst₅ : Alg65LoopState ξ δ x x.n (x.G.cap δ) x.Z id s₅ := by
    refine ⟨.refl, hG_arr₅, ?_, ?_, hr26_5, hr27_5, hr28_5⟩
    · rw [harr₅ (18 + p + 1) (by omega) (by omega)]; exact hZ_arr₄
    · rw [harr₅ (18 + p + 2) (by omega) (by omega), harr₄ (18 + p + 2) (by omega)]
      exact hemb₁
  rcases alg65Loop_exec ξ δ x hw3 hn0_w h2n0_w hp_w hC_n_w hm3_cap_w hedges_cap_w hpow_64_w
      x.n (x.G.cap δ) x.Z id hst₅ with
    ⟨n', G', Z', emb', s₆, t₆, hex₆, ht₆, hedges_out, hst₆⟩
  -- 6. `alg65WriteOutProg p`
  have hnr_le : n' ≤ x.n := hst₆.trace.le_num_vertices
  have hn'_w : n' < 2 ^ w := by omega
  have hm'_le_cap : G'.numActivePairs ≤ (x.G.cap δ).numActivePairs := hst₆.trace.numActivePairs_le
  have hm3_out_w : 2 + 3 * G'.numActivePairs < 2 ^ w := by omega
  have h2len_out_r_w : 2 * (2 + 3 * G'.numActivePairs + n') < 2 ^ w := by omega
  have hedges_out_le : G'.numEdges ≤ (x.G.cap δ).numEdges := hst₆.trace.numEdges_le
  have hedges_out_w : G'.numEdges < 2 ^ w := by omega
  rcases alg65WriteOutProg_exec p G' emb' hw3 hn0_w hn'_w hm3_out_w h2len_out_r_w hedges_out_w
      hst₆.hG_arr hst₆.hemb_arr hst₆.hr26 hst₆.hr27 with
    ⟨s₇, t₇, hex₇, ht₇, hout₇⟩
  -- 7. Total running time and output validity
  refine ⟨s₇, 3 + (t₁ + (3 + (6 + (t₄ + (t₅ + (t₆ + t₇)))))),
    .seq hex₀' (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))),
    ?_, ?_⟩
  · -- Step count bound `≤ (450 + K_iter) * (x.n + 1) ^ 3`
    let S := x.n + 1
    have hS_pos : 1 ≤ S := by omega
    have hS3_eq : S ^ 3 = S * S ^ 2 := by
      change S ^ (2 + 1) = S * S ^ 2
      rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm]
    have hS2_eq : S ^ 2 = x.n * x.n + 2 * x.n + 1 := by
      rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    have hS2_le_S3 : S ^ 2 ≤ S ^ 3 := by
      rw [hS3_eq]; exact Nat.le_mul_of_pos_left (S ^ 2) hS_pos
    have h1_S3 : 1 ≤ S ^ 3 := le_trans (by omega : 1 ≤ S ^ 2) hS2_le_S3
    have hn_S3 : x.n ≤ S ^ 3 := le_trans (by omega : x.n ≤ S ^ 2) hS2_le_S3
    have hm_S2 : x.G.numActivePairs ≤ S ^ 2 := by omega
    have hm_S3 : x.G.numActivePairs ≤ S ^ 3 := le_trans hm_S2 hS2_le_S3
    have ht₆_bound : t₆ ≤ 5 * S ^ 2 + K_iter * S ^ 3 := by
      have h1 : x.n * (5 + K_iter * S ^ 2) = x.n * 5 + x.n * (K_iter * S ^ 2) :=
        Nat.mul_add x.n 5 (K_iter * S ^ 2)
      have h2 : x.n * (K_iter * S ^ 2) ≤ S * (K_iter * S ^ 2) :=
        Nat.mul_le_mul_right (K_iter * S ^ 2) (by omega)
      have h3 : S * (K_iter * S ^ 2) = K_iter * S ^ 3 := by
        rw [hS3_eq, ← Nat.mul_assoc, Nat.mul_comm S K_iter, Nat.mul_assoc]
      have h4 : 5 + x.n * 5 ≤ 5 * S ^ 2 := by omega
      rw [h3] at h2
      rw [h1] at ht₆
      generalize K_iter * S ^ 3 = MK at h2 ht₆ ⊢
      omega
    have h5S2_le : 5 * S ^ 2 ≤ 5 * S ^ 3 := Nat.mul_le_mul_left 5 hS2_le_S3
    have hrest_S3 :
        3 + t₁ + 3 + 6 + t₄ + t₅ + 5 * S ^ 2 + t₇ ≤ 450 * S ^ 3 := by
      have hm'_S3 : G'.numActivePairs ≤ S ^ 3 := le_trans (le_trans hm'_le_cap hcap_le_G) hm_S3
      have hn'_S3 : n' ≤ S ^ 3 := le_trans hnr_le hn_S3
      clear ht₆ ht₆_bound hpow_full h2_pow_lt hpow_64_w hC_le_pow hC_n_w
      omega
    have htotal_expand :
        (450 + K_iter) * S ^ 3 = 450 * S ^ 3 + K_iter * S ^ 3 :=
      Nat.add_mul 450 K_iter (S ^ 3)
    change _ ≤ (450 + K_iter) * S ^ 3
    rw [htotal_expand]
    generalize 450 * S ^ 3 = M450 at hrest_S3 ⊢
    generalize K_iter * S ^ 3 = MK at ht₆_bound ⊢
    clear ht₁ ht₄ ht₅ ht₆ ht₇ hpow_full h2_pow_lt hpow_64_w hC_le_pow hC_n_w
    omega
  · -- Output validity (`IsValidAlg65Output ξ δ x (decAlg65Out x.n (s₇.arrs outArr))`)
    dsimp only
    rw [hout₇, decAlg65Out_eq G' emb' hnr_le]
    have hle_mult : ∀ u v : Fin n', G'.edgeMult u v ≤ x.G.edgeMult (emb' u) (emb' v) := by
      intro u v
      rw [hst₆.trace.induce_eq, MultiDigraph.induce_edgeMult]
      dsimp [MultiDigraph.cap]
      exact Nat.min_le_left _ _
    have hncard_le :
        (G'.toEmbeddedGMDigraph emb').edgeSet.ncard ≤
          alg65Const ξ δ * (G'.toEmbeddedGMDigraph emb').vertexSet.ncard := by
      rw [G'.ncard_edgeSet_toEmbeddedGMDigraph hst₆.trace.injective_emb,
        G'.ncard_vertexSet_toEmbeddedGMDigraph hst₆.trace.injective_emb]
      exact hedges_out
    exact ⟨hst₆.trace.injective_emb, hle_mult, hst₆.trace.subset_image_univ,
      hedges_out, x.G.isSubdigraph_toEmbeddedGMDigraph hle_mult,
      G'.toNatSet_subset_toEmbeddedGMDigraph hst₆.trace.image_Z,
      hst₆.trace.hasSameDeltaFolioRel_of_cap x.hZ, hncard_le,
      Z', hst₆.trace.image_Z, hst₆.trace.card_Z,
      hst₆.trace.forall_isDeltaFolioRep_of_cap x.hZ, hst₆.trace⟩

end GraphMinor.Compute


