module

public import GraphMinor.Crossing.Statements
import GraphMinor.Crossing.CutSec2Fan
import GraphMinor.Menger.SimpleGraph
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sections 2.1 and 2.2 of the crossing extractor: the bounded-flow primitive and maximum source cut

This file proves the four flow and cut statements of Sections 2.1 and 2.2 of
`docs/crossing/crossing_extractor.tex`:
* `sec21Paths_proved : Sec21PathsStatement`
* `sec21Augment_proved : Sec21AugmentStatement`
* `sec21Cut_proved : Sec21CutStatement`
* `sec22_proved : Sec22Statement`
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set Finset

universe u

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ### Part 1: General network flow and cut lemmas -/

omit [DecidableEq N] in
theorem IsFlow.flowValue_eq_zero {cap : N → N → ℕ} {src snk : N} {f : N → N → ℕ}
    (hf : IsFlow cap src snk f) {a : N} (hsrc : a ≠ src) (hsnk : a ≠ snk) :
    flowValue a f = 0 := by
  unfold flowValue
  have hcons := hf.2 a hsrc hsnk
  have hcast : (∑ b, (f b a : ℤ)) = ∑ b, (f a b : ℤ) := by
     exact_mod_cast hcons
  omega

/-- **Flow across a cut**: for any flow `f` from `src` to `snk` and any cut `C` with `src ∈ C`
and `snk ∉ C`, the flow value equals the flow from `C` to `Cᶜ` minus the flow from `Cᶜ` to `C`. -/
theorem flowValue_eq_sum_cut {cap : N → N → ℕ} {src snk : N} {f : N → N → ℕ}
    (hf : IsFlow cap src snk f) (C : Finset N) (hsrc : src ∈ C) (hsnk : snk ∉ C) :
    flowValue src f =
      (∑ a ∈ C, ∑ b ∈ Cᶜ, (f a b : ℤ)) - ∑ a ∈ C, ∑ b ∈ Cᶜ, (f b a : ℤ) := by
  have hsum_net : flowValue src f = ∑ a ∈ C, flowValue a f := by
    refine (Finset.sum_eq_single (f := fun a => flowValue a f) src
      (fun a ha hne => ?_) (fun h => absurd hsrc h)).symm
    exact hf.flowValue_eq_zero hne (fun h => hsnk (h ▸ ha))
  have hsplit_out :
      ∑ a ∈ C, ∑ b, (f a b : ℤ) =
        (∑ a ∈ C, ∑ b ∈ C, (f a b : ℤ)) + ∑ a ∈ C, ∑ b ∈ Cᶜ, (f a b : ℤ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (Finset.sum_add_sum_compl C (fun b => (f a b : ℤ))).symm
  have hsplit_in :
      ∑ a ∈ C, ∑ b, (f b a : ℤ) =
        (∑ a ∈ C, ∑ b ∈ C, (f b a : ℤ)) + ∑ a ∈ C, ∑ b ∈ Cᶜ, (f b a : ℤ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (Finset.sum_add_sum_compl C (fun b => (f b a : ℤ))).symm
  have hcomm : (∑ a ∈ C, ∑ b ∈ C, (f b a : ℤ)) = ∑ a ∈ C, ∑ b ∈ C, (f a b : ℤ) :=
    Finset.sum_comm
  rw [hsum_net]
  unfold flowValue
  rw [Finset.sum_sub_distrib, hsplit_out, hsplit_in, hcomm]
  omega

/-- Weak duality: the value of any flow is bounded by the capacity of any cut separating `src`
from `snk`. -/
theorem flowValue_le_cutCap {cap : N → N → ℕ} {src snk : N} {f : N → N → ℕ}
    (hf : IsFlow cap src snk f) (C : Finset N) (hsrc : src ∈ C) (hsnk : snk ∉ C) :
    flowValue src f ≤ ∑ a ∈ C, ∑ b ∈ Cᶜ, (cap a b : ℤ) := by
  rw [flowValue_eq_sum_cut hf C hsrc hsnk]
  have h1 : (∑ a ∈ C, ∑ b ∈ Cᶜ, (f a b : ℤ)) ≤ ∑ a ∈ C, ∑ b ∈ Cᶜ, (cap a b : ℤ) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    exact_mod_cast hf.1 a b
  have h2 : (0 : ℤ) ≤ ∑ a ∈ C, ∑ b ∈ Cᶜ, (f b a : ℤ) := by
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    omega
  omega

/-- If no residual arc crosses from `C` to `Cᶜ`, the flow value equals the cut capacity. -/
theorem flowValue_eq_cutCap_of_no_resAdj {cap : N → N → ℕ} {src snk : N} {f : N → N → ℕ}
    (hf : IsFlow cap src snk f) (C : Finset N) (hsrc : src ∈ C) (hsnk : snk ∉ C)
    (hno : ∀ a ∈ C, ∀ b ∈ Cᶜ, ¬ ResAdj cap f a b) :
    flowValue src f = ∑ a ∈ C, ∑ b ∈ Cᶜ, (cap a b : ℤ) := by
  rw [flowValue_eq_sum_cut hf C hsrc hsnk]
  have hout : (∑ a ∈ C, ∑ b ∈ Cᶜ, (f a b : ℤ)) = ∑ a ∈ C, ∑ b ∈ Cᶜ, (cap a b : ℤ) := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have hnot := hno a ha b hb
    unfold ResAdj at hnot
    have hle := hf.1 a b
    omega
  have hin : (∑ a ∈ C, ∑ b ∈ Cᶜ, (f b a : ℤ)) = 0 := by
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    have hnot := hno a ha b hb
    unfold ResAdj at hnot
    omega
  omega

/-- Conversely, if the flow value equals the capacity of a cut `C`, then no residual arc crosses
from `C` to `Cᶜ`. -/
theorem no_resAdj_of_flowValue_eq_cutCap {cap : N → N → ℕ} {src snk : N} {f : N → N → ℕ}
    (hf : IsFlow cap src snk f) (C : Finset N) (hsrc : src ∈ C) (hsnk : snk ∉ C)
    (heq : flowValue src f = ∑ a ∈ C, ∑ b ∈ Cᶜ, (cap a b : ℤ)) :
    ∀ a ∈ C, ∀ b ∈ Cᶜ, ¬ ResAdj cap f a b := by
  intro a₀ ha₀ b₀ hb₀ hres
  have hval := flowValue_eq_sum_cut hf C hsrc hsnk
  have hle_inner :
      ∀ a ∈ C, (∑ b ∈ Cᶜ, (f a b : ℤ)) - (∑ b ∈ Cᶜ, (f b a : ℤ)) ≤ ∑ b ∈ Cᶜ, (cap a b : ℤ) := by
    intro a _
    have h1 : (∑ b ∈ Cᶜ, (f a b : ℤ)) ≤ ∑ b ∈ Cᶜ, (cap a b : ℤ) :=
      Finset.sum_le_sum fun b _ => by exact_mod_cast hf.1 a b
    have h2 : (0 : ℤ) ≤ ∑ b ∈ Cᶜ, (f b a : ℤ) :=
      Finset.sum_nonneg fun b _ => by positivity
    omega
  have hlt_a₀ :
      (∑ b ∈ Cᶜ, (f a₀ b : ℤ)) - (∑ b ∈ Cᶜ, (f b a₀ : ℤ)) < ∑ b ∈ Cᶜ, (cap a₀ b : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_lt_sum (fun b _ => by have := hf.1 a₀ b; omega) ⟨b₀, hb₀, ?_⟩
    unfold ResAdj at hres
    have := hf.1 a₀ b₀
    omega
  have hlt_outer :
      (∑ a ∈ C, ((∑ b ∈ Cᶜ, (f a b : ℤ)) - ∑ b ∈ Cᶜ, (f b a : ℤ))) <
        ∑ a ∈ C, ∑ b ∈ Cᶜ, (cap a b : ℤ) :=
    Finset.sum_lt_sum hle_inner ⟨a₀, ha₀, hlt_a₀⟩
  rw [Finset.sum_sub_distrib, ← hval, heq] at hlt_outer
  exact lt_irrefl _ hlt_outer

/-- If no residual arc leaves `C`, no vertex in `C` can reach a vertex outside `C` in the
residual graph. -/
theorem not_resReach_of_no_resAdj {cap : N → N → ℕ} {f : N → N → ℕ} (C : Finset N)
    (hno : ∀ a ∈ C, ∀ b ∈ Cᶜ, ¬ ResAdj cap f a b) {x y : N}
    (hx : x ∈ C) (hy : y ∉ C) :
    ¬ ResReach cap f x y := by
  intro hreach
  have hmem : ∀ u, Relation.ReflTransGen (ResAdj cap f) u y → u ∈ C → y ∈ C := by
    intro u hu
    induction hu using Relation.ReflTransGen.head_induction_on with
    | refl => exact id
    | @head a b hab _ ih =>
      intro ha
      by_cases hb : b ∈ C
      · exact ih hb
      · exact False.elim (hno a ha b (Finset.mem_compl.mpr hb) hab)
  exact hy (hmem x hreach hx)

omit [Fintype N] [DecidableEq N] in
/-- No residual arc leaves `sinkCut`. -/
theorem not_resAdj_of_mem_sinkCut {cap : N → N → ℕ} {f : N → N → ℕ} {snk a b : N}
    (ha : a ∈ sinkCut cap f snk) (hb : b ∉ sinkCut cap f snk) :
    ¬ ResAdj cap f a b := by
  intro hab
  have hreach_b : ResReach cap f b snk := by
    simpa [sinkCut] using hb
  exact ha (Relation.ReflTransGen.head hab hreach_b)

/-! ### Part 2: Augmenting along a simple residual path (`Sec21AugmentStatement`) -/

omit [Fintype N] in
/-- Any residual reachability `ResReach cap f a b` yields a nodup vertex list from `a` to `b`
forming a chain in `ResAdj cap f`. -/
private theorem exists_nodup_chain_of_resReach {cap : N → N → ℕ} {f : N → N → ℕ} {a b : N}
    (h : ResReach cap f a b) :
    ∃ L : List N, L.Nodup ∧ L.IsChain (ResAdj cap f) ∧ L.head? = some a ∧ L.getLast? = some b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exact ⟨[b], List.nodup_singleton b, List.isChain_singleton b, rfl, rfl⟩
  | @head u v huv _ ih =>
    rcases ih with ⟨L, hnd, hch, hhead, hlast⟩
    by_cases hu : u ∈ L
    · refine ⟨u :: L.drop (L.idxOf u + 1), ?_, ?_, rfl, ?_⟩
      · have hsplit : (L.take (L.idxOf u + 1) ++ L.drop (L.idxOf u + 1)).Nodup := by
          rwa [List.take_append_drop]
        have hlt : L.idxOf u < L.length := List.idxOf_lt_length_of_mem hu
        have htake : L.take (L.idxOf u + 1) = L.take (L.idxOf u) ++ [u] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.getElem_idxOf]
        rw [htake, List.append_assoc, List.singleton_append] at hsplit
        exact (List.nodup_append.mp hsplit).2.1
      · have hlt : L.idxOf u < L.length := List.idxOf_lt_length_of_mem hu
        have hdrop : L.drop (L.idxOf u) = u :: L.drop (L.idxOf u + 1) := by
          rw [← List.getElem_cons_drop hlt, List.getElem_idxOf]
        rw [← hdrop]
        exact hch.drop (L.idxOf u)
      · have hlt : L.idxOf u < L.length := List.idxOf_lt_length_of_mem hu
        have hdrop : L.drop (L.idxOf u) = u :: L.drop (L.idxOf u + 1) := by
          rw [← List.getElem_cons_drop hlt, List.getElem_idxOf]
        rw [← hdrop, List.getLast?_drop]
        simp only [Nat.not_le_of_gt hlt, ↓reduceIte, hlast]
    · cases L with
      | nil => simp at hhead
      | cons w rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst w
        refine ⟨u :: v :: rest, List.nodup_cons.mpr ⟨hu, hnd⟩,
          List.IsChain.cons_cons huv hch, rfl, ?_⟩
        rw [List.getLast?_cons_cons]
        exact hlast

/-- Augmenting flow along a single residual step `u → v`. -/
noncomputable def augEdge (cap f : N → N → ℕ) (u v : N) (a b : N) : ℕ :=
  if f u v < cap u v then
    if a = u ∧ b = v then f u v + 1 else f a b
  else
    if a = v ∧ b = u then f v u - 1 else f a b

omit [Fintype N] in
private theorem augEdge_le_cap {cap f : N → N → ℕ} {u v : N}
    (hle : ∀ a b, f a b ≤ cap a b) (_hres : ResAdj cap f u v) :
    ∀ a b, augEdge cap f u v a b ≤ cap a b := by
  intro a b
  unfold augEdge
  split_ifs with h1 h2 h3
  · rcases h2 with ⟨ha, hb⟩; subst a b; omega
  · exact hle a b
  · rcases h3 with ⟨ha, hb⟩; subst a b; have := hle v u; omega
  · exact hle a b

omit [Fintype N] in
private theorem augEdge_eq_of_ne {cap f : N → N → ℕ} {u v a b : N}
    (hau : a ≠ u) (hbu : b ≠ u) :
    augEdge cap f u v a b = f a b := by
  unfold augEdge
  split_ifs with h1 h2 h3
  · exact absurd h2.1 hau
  · rfl
  · exact absurd h3.2 hbu
  · rfl

omit [Fintype N] in
private theorem resAdj_augEdge_iff {cap f : N → N → ℕ} {u v a b : N}
    (hau : a ≠ u) (hbu : b ≠ u) :
    ResAdj cap (augEdge cap f u v) a b ↔ ResAdj cap f a b := by
  unfold ResAdj
  rw [augEdge_eq_of_ne hau hbu, augEdge_eq_of_ne hbu hau]

private theorem sum_update_pair_add (f : N → N → ℕ) (u v a : N) :
    (∑ b, ((if a = u ∧ b = v then f u v + 1 else f a b : ℕ) : ℤ)) =
      (∑ b, (f a b : ℤ)) + if a = u then 1 else 0 := by
  by_cases ha : a = u
  · subst ha
    simp only [true_and, ↓reduceIte]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    simp only [↓reduceIte]
    have heq :
        (∑ x ∈ Finset.univ.erase v, ((if x = v then f a v + 1 else f a x : ℕ) : ℤ)) =
          ∑ x ∈ Finset.univ.erase v, (f a x : ℤ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_erase] at hx
      simp [hx.1]
    rw [heq]
    push_cast
    ring
  · simp [ha]

private theorem sum_update_pair_add_in (f : N → N → ℕ) (u v a : N) :
    (∑ b, ((if b = u ∧ a = v then f u v + 1 else f b a : ℕ) : ℤ)) =
      (∑ b, (f b a : ℤ)) + if a = v then 1 else 0 := by
  by_cases ha : a = v
  · subst ha
    simp only [and_true, ↓reduceIte]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
    simp only [↓reduceIte]
    have heq :
        (∑ x ∈ Finset.univ.erase u, ((if x = u then f u a + 1 else f x a : ℕ) : ℤ)) =
          ∑ x ∈ Finset.univ.erase u, (f x a : ℤ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_erase] at hx
      simp [hx.1]
    rw [heq]
    push_cast
    ring
  · simp [ha]

private theorem sum_update_pair_sub (f : N → N → ℕ) (u v a : N) (hpos : 0 < f v u) :
    (∑ b, ((if a = v ∧ b = u then f v u - 1 else f a b : ℕ) : ℤ)) =
      (∑ b, (f a b : ℤ)) - if a = v then 1 else 0 := by
  by_cases ha : a = v
  · subst ha
    simp only [true_and, ↓reduceIte]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
    simp only [↓reduceIte]
    have heq :
        (∑ x ∈ Finset.univ.erase u, ((if x = u then f a u - 1 else f a x : ℕ) : ℤ)) =
          ∑ x ∈ Finset.univ.erase u, (f a x : ℤ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_erase] at hx
      simp [hx.1]
    rw [heq]
    omega
  · simp [ha]

private theorem sum_update_pair_sub_in (f : N → N → ℕ) (u v a : N) (hpos : 0 < f v u) :
    (∑ b, ((if b = v ∧ a = u then f v u - 1 else f b a : ℕ) : ℤ)) =
      (∑ b, (f b a : ℤ)) - if a = u then 1 else 0 := by
  by_cases ha : a = u
  · subst ha
    simp only [and_true, ↓reduceIte]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    simp only [↓reduceIte]
    have heq :
        (∑ x ∈ Finset.univ.erase v, ((if x = v then f v a - 1 else f x a : ℕ) : ℤ)) =
          ∑ x ∈ Finset.univ.erase v, (f x a : ℤ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_erase] at hx
      simp [hx.1]
    rw [heq]
    omega
  · simp [ha]

private theorem flowValue_augEdge {cap f : N → N → ℕ} {u v : N}
    (hres : ResAdj cap f u v) (a : N) :
    flowValue a (augEdge cap f u v) =
      flowValue a f + (if a = u then 1 else 0) - (if a = v then 1 else 0) := by
  unfold flowValue augEdge
  by_cases hlt : f u v < cap u v
  · simp only [hlt, ↓reduceIte]
    rw [sum_update_pair_add, sum_update_pair_add_in]
    ring
  · have hpos : 0 < f v u := hres.resolve_left hlt
    simp only [hlt, ↓reduceIte]
    rw [sum_update_pair_sub f u v a hpos, sum_update_pair_sub_in f u v a hpos]
    ring

/-- Augmenting flow along a chain of vertices `L`. -/
noncomputable def augChain (cap f : N → N → ℕ) : List N → (N → N → ℕ)
  | u :: v :: rest => augChain cap (augEdge cap f u v) (v :: rest)
  | _ => f

private theorem augChain_props {cap : N → N → ℕ} :
    ∀ (L : List N) (f : N → N → ℕ) (u v : N),
      L.Nodup → L.IsChain (ResAdj cap f) →
      L.head? = some u → L.getLast? = some v →
      (∀ a b, f a b ≤ cap a b) →
      let f' := augChain cap f L
      (∀ a b, f' a b ≤ cap a b) ∧
        ∀ a : N, flowValue a f' = flowValue a f + (if a = u then 1 else 0) - (if a = v then 1 else 0)
  | [], _, _, _, _, _, hhead, _, _ => by simp at hhead
  | [x], f, u, v, _, _, hhead, hlast, hle => by
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
    subst hhead hlast
    refine ⟨hle, fun a => ?_⟩
    simp [augChain]
  | x :: y :: rest, f, u, v, hnd, hch, hhead, hlast, hle => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rw [List.getLast?_cons_cons] at hlast
    have hnd_cons := List.nodup_cons.mp hnd
    have hx_not_mem : x ∉ y :: rest := hnd_cons.1
    have hnd_tail : (y :: rest).Nodup := hnd_cons.2
    have hxy : ResAdj cap f x y := List.IsChain.rel_head? hch rfl
    have hch_tail : (y :: rest).IsChain (ResAdj cap f) := List.IsChain.tail hch
    let f₁ := augEdge cap f x y
    have hle₁ : ∀ a b, f₁ a b ≤ cap a b := augEdge_le_cap hle hxy
    have hch₁ : (y :: rest).IsChain (ResAdj cap f₁) := by
      refine hch_tail.imp_of_mem_imp fun a b ha hb hab => ?_
      have hax : a ≠ x := fun h => hx_not_mem (h ▸ ha)
      have hbx : b ≠ x := fun h => hx_not_mem (h ▸ hb)
      exact (resAdj_augEdge_iff hax hbx).mpr hab
    obtain ⟨hle', hnet'⟩ :=
      augChain_props (y :: rest) f₁ y v hnd_tail hch₁ rfl hlast hle₁
    refine ⟨hle', fun a => ?_⟩
    change flowValue a (augChain cap f₁ (y :: rest)) = _
    rw [hnet' a, flowValue_augEdge hxy a]
    ring

/-- **Augmentation** (Section 2.1): a residual path from source to sink gives a flow of value one
more. -/
theorem sec21Augment_proved : Sec21AugmentStatement := by
  intro W _ _ J T z x k f ℓ hf hval hreach
  let cap := splitCap J T z x k
  have hne_src_snk : ((z, true) : W × Bool) ≠ (x, false) := by simp
  obtain ⟨L, hnd, hch, hhead, hlast⟩ := exists_nodup_chain_of_resReach hreach
  obtain ⟨hle', hnet'⟩ := augChain_props L f (z, true) (x, false) hnd hch hhead hlast hf.1
  let f' := augChain cap f L
  refine ⟨f', ⟨hle', ?_⟩, ?_⟩
  · intro a hasrc hasnk
    have h0 : flowValue a f' =
        flowValue a f + (if a = (z, true) then 1 else 0) - (if a = (x, false) then 1 else 0) :=
      hnet' a
    simp [hasrc, hasnk, hf.flowValue_eq_zero hasrc hasnk] at h0
    unfold flowValue at h0
    have hsum_eq : (∑ b, (f' b a : ℤ)) = ∑ b, (f' a b : ℤ) := by omega
    exact_mod_cast hsum_eq
  · rw [hnet' (z, true)]
    simp [hne_src_snk, hval]

/-! ### Part 3: The split network cut of a vertex separator (`Sec21PathsStatement`) -/

variable {W : Type u} [Fintype W] [DecidableEq W]

open Classical in
/-- The split-network cut associated with a vertex separator `X` and its open source side
`sourceSide J T x X`. -/
noncomputable def sepCut (J : SimpleGraph W) (T : Set W) (x : W) (X : Finset W) :
    Finset (W × Bool) :=
  Finset.univ.filter fun p : W × Bool =>
    match p with
    | (v, false) => v ∈ sourceSide J T x X ∨ v ∈ X
    | (v, true) => v ∈ sourceSide J T x X

open Classical in
omit [DecidableEq W] in
theorem mem_sepCut_false {J : SimpleGraph W} {T : Set W} {x v : W} {X : Finset W} :
    (v, false) ∈ sepCut J T x X ↔ v ∈ sourceSide J T x X ∨ v ∈ X := by
  simp [sepCut]

open Classical in
omit [DecidableEq W] in
theorem mem_sepCut_true {J : SimpleGraph W} {T : Set W} {x v : W} {X : Finset W} :
    (v, true) ∈ sepCut J T x X ↔ v ∈ sourceSide J T x X := by
  simp [sepCut]

omit [Fintype W] in
theorem sourceSide_closed_adj {J : SimpleGraph W} {T : Set W} {x u v : W} {X : Finset W}
    (hu : u ∈ sourceSide J T x X) (hvT : v ∈ T) (hadj : J.Adj u v) :
    v ∈ sourceSide J T x X ∨ v ∈ X := by
  by_cases hvX : v ∈ X
  · exact Or.inr hvX
  · refine Or.inl ⟨hvT, hvX, fun hr => hu.2.2 ?_⟩
    exact (ReachIn.of_adj (T := T \ X) hadj ⟨hu.1, hu.2.1⟩ ⟨hvT, hvX⟩).trans hr

/-- Every arc crossing `sepCut J T x X` has capacity `0`, except `(v, false) → (v, true)` for
`v ∈ X`, which has capacity `1`. -/
theorem splitCap_sepCut_eq {J : SimpleGraph W} {T : Set W} {z x : W} {k : ℕ} {X : Finset W}
    (hsep : IsSeparator J T z x X) {a b : W × Bool}
    (ha : a ∈ sepCut J T x X) (hb : b ∈ (sepCut J T x X)ᶜ) :
    splitCap J T z x k a b =
      if ∃ v ∈ X, a = (v, false) ∧ b = (v, true) then 1 else 0 := by
  rw [Finset.mem_compl] at hb
  rcases a with ⟨u, _ | _⟩ <;> rcases b with ⟨v, _ | _⟩
  · simp [splitCap]
  · rw [mem_sepCut_false] at ha
    rw [mem_sepCut_true] at hb
    dsimp [splitCap]
    by_cases huv : u = v
    · subst huv
      have huX : u ∈ X := ha.resolve_left hb
      have hu_sub := hsep.1 huX
      have huT : u ∈ T := hu_sub.1
      have huz : u ≠ z := fun h => hu_sub.2 (by simp [h])
      have hux : u ≠ x := fun h => hu_sub.2 (by simp [h])
      simp [huX, huT, huz, hux]
    · simp [huv]
  · rw [mem_sepCut_true] at ha
    rw [mem_sepCut_false] at hb
    dsimp [splitCap]
    have hnot_adj : ¬ (u ∈ T ∧ v ∈ T ∧ J.Adj u v) := by
      rintro ⟨_, hvT, hadj⟩
      exact hb (sourceSide_closed_adj ha hvT hadj)
    simp [hnot_adj]
  · simp [splitCap]

/-- The cut capacity of `sepCut J T x X` equals `X.card`. -/
theorem sum_splitCap_sepCut {J : SimpleGraph W} {T : Set W} {z x : W} (k : ℕ) {X : Finset W}
    (hsep : IsSeparator J T z x X) :
    (∑ a ∈ sepCut J T x X, ∑ b ∈ (sepCut J T x X)ᶜ, (splitCap J T z x k a b : ℤ)) = X.card := by
  let C := sepCut J T x X
  have h1 :
      (∑ a ∈ C, ∑ b ∈ Cᶜ, (splitCap J T z x k a b : ℤ)) =
        ∑ a ∈ C, ∑ b ∈ Cᶜ, if ∃ v ∈ X, a = (v, false) ∧ b = (v, true) then (1 : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [splitCap_sepCut_eq hsep ha hb]
    split_ifs <;> rfl
  rw [h1]
  have h2 :
      ∀ v ∈ X,
        (v, false) ∈ C ∧ (v, true) ∈ Cᶜ := by
    intro v hvX
    refine ⟨mem_sepCut_false.mpr (Or.inr hvX), Finset.mem_compl.mpr ?_⟩
    rw [mem_sepCut_true]
    intro hvU
    exact hvU.2.1 hvX
  have h3 :
      (∑ a ∈ C, ∑ b ∈ Cᶜ, if ∃ v ∈ X, a = (v, false) ∧ b = (v, true) then (1 : ℤ) else 0) =
        ∑ v ∈ X, (1 : ℤ) := by
    trans (∑ a ∈ X.image (fun v => (v, false)),
      ∑ b ∈ Cᶜ, if ∃ v ∈ X, a = (v, false) ∧ b = (v, true) then (1 : ℤ) else 0)
    · refine (Finset.sum_subset (fun a ha => ?_) (fun a _ ha_not => ?_)).symm
      · simp only [Finset.mem_image] at ha
        rcases ha with ⟨v, hvX, rfl⟩
        exact (h2 v hvX).1
      · refine Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right_iff]
        rintro ⟨v, hvX, rfl, rfl⟩
        exact False.elim (ha_not (Finset.mem_image_of_mem _ hvX))
    · rw [Finset.sum_image (fun u _ v _ h => by injection h)]
      refine Finset.sum_congr rfl fun v hvX => ?_
      rw [Finset.sum_eq_single (v, true)]
      · simp [hvX]
      · intro b _ hne
        rw [ite_eq_right_iff]
        rintro ⟨w, _, h1, h2⟩
        cases h1
        exact False.elim (hne h2)
      · intro h
        exact False.elim (h (h2 v hvX).2)
  rw [h3, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Any vertex separator `X` between `z` and `x` in `J` on `T` has size at least the value of any
flow `f` in the split network. -/
theorem le_card_separator_of_isFlow {J : SimpleGraph W} {T : Set W} {z x : W} {k ℓ : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hzT : z ∈ T) (hxT : x ∈ T)
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f)
    (hval : flowValue (z, true) f = ℓ)
    {X : Finset W} (hsep : IsSeparator J T z x X) :
    ℓ ≤ X.card := by
  let C := sepCut J T x X
  have hzC : (z, true) ∈ C := by
    rw [mem_sepCut_true]
    refine ⟨hzT, fun hzX => (hsep.1 hzX).2 (by simp), hsep.2⟩
  have hxC : (x, false) ∉ C := by
    rw [mem_sepCut_false]
    rintro (hxU | hxX)
    · exact hxU.2.2 (ReachIn.refl ⟨hxT, hxU.2.1⟩)
    · exact (hsep.1 hxX).2 (by simp)
  have hle := flowValue_le_cutCap hf C hzC hxC
  rw [hval, sum_splitCap_sepCut k hsep] at hle
  exact_mod_cast hle

/-- The induced subgraph on `T \ {z, x}` used to apply Menger's theorem between the neighbors of `z`
and the neighbors of `x`. -/
private def innerGraph (J : SimpleGraph W) (T : Set W) (z x : W) : SimpleGraph W where
  Adj a b := J.Adj a b ∧ a ∈ T ∧ b ∈ T ∧ a ≠ z ∧ a ≠ x ∧ b ≠ z ∧ b ≠ x
  symm := ⟨fun _ _ ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1.symm, h3, h2, h6, h7, h4, h5⟩⟩
  loopless := ⟨fun _ h => J.loopless.irrefl _ h.1⟩

private abbrev innerHom (J : SimpleGraph W) (T : Set W) (z x : W) :
    innerGraph J T z x →g J where
  toFun a := a
  map_rel' h := h.1

omit [Fintype W] [DecidableEq W] in
private theorem mem_of_mem_support_innerWalk {J : SimpleGraph W} {T : Set W} {z x a b : W}
    (ha : a ∈ T ∧ a ≠ z ∧ a ≠ x) (w : (innerGraph J T z x).Walk a b) :
    ∀ y ∈ w.support, y ∈ T ∧ y ≠ z ∧ y ≠ x := by
  induction w with
  | nil =>
    intro y hy
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    exact hy ▸ ha
  | @cons u v b hadj rest ih =>
    intro y hy
    rw [Walk.support_cons, List.mem_cons] at hy
    exact hy.elim (fun h => h ▸ ha) (ih ⟨hadj.2.2.1, hadj.2.2.2.2.2.1, hadj.2.2.2.2.2.2⟩ y)

omit [Fintype W] in
/-- Any simple path in `J` from `a ∈ T \ {z, x}` to `w = x` that stays in `T \ X` and avoids `z`
yields a walk in `innerGraph J T z x` from `a` to a neighbor of `x` avoiding `X`. -/
private theorem exists_innerWalk_of_walk {J : SimpleGraph W} {T : Set W} {z x : W}
    {X : Finset W} {a w : W} (q : J.Walk a w) :
    w = x →
    z ∉ q.support →
    (∀ y ∈ q.support, y ∈ T \ X) →
    a ≠ x →
    ∃ b : W, b ∈ T ∧ b ≠ z ∧ b ≠ x ∧ J.Adj b x ∧
      ∃ w₀ : (innerGraph J T z x).Walk a b, ∀ y ∈ w₀.support, y ∉ X := by
  induction q with
  | nil =>
    intro hw _ _ hax
    exact False.elim (hax hw)
  | @cons a u w hadj rest ih =>
    intro hw hz_not hsupp hax
    subst w
    have ha_TX : a ∈ T \ X := hsupp a (Walk.start_mem_support _)
    have haz : a ≠ z := fun h => hz_not (h ▸ Walk.start_mem_support _)
    have hz_rest : z ∉ rest.support := fun h => hz_not (List.mem_cons_of_mem _ h)
    have hsupp_rest : ∀ y ∈ rest.support, y ∈ T \ X :=
      fun y hy => hsupp y (List.mem_cons_of_mem _ hy)
    by_cases hux : u = x
    · subst u
      refine ⟨a, ha_TX.1, haz, hax, hadj, .nil, fun y hy => ?_⟩
      simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
      exact hy ▸ ha_TX.2
    · obtain ⟨b, hbT, hbz, hbx, hadj_bx, w₀, hw₀⟩ := ih rfl hz_rest hsupp_rest hux
      have hu_TX : u ∈ T \ X := hsupp_rest u (Walk.start_mem_support _)
      have huz : u ≠ z := fun h => hz_rest (h ▸ Walk.start_mem_support _)
      have hadj₀ : (innerGraph J T z x).Adj a u :=
        ⟨hadj, ha_TX.1, hu_TX.1, haz, hax, huz, hux⟩
      refine ⟨b, hbT, hbz, hbx, hadj_bx, .cons hadj₀ w₀, fun y hy => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hy
      exact hy.elim (fun h => h ▸ ha_TX.2) (hw₀ y)

open Classical in
/-- **A flow gives disjoint paths** (Section 2.1): a flow of value `ℓ` from `z_out` to `x_in` in
the split network gives `ℓ` internally disjoint `z`-`x` paths. -/
theorem sec21Paths_proved : Sec21PathsStatement := by
  intro W _ _ J T z x k ℓ f hzT hxT hzx hadj_zx hf hval
  let K₀ := innerGraph J T z x
  let A₀ : Set W := {u | u ∈ T ∧ u ≠ z ∧ u ≠ x ∧ J.Adj z u}
  let B₀ : Set W := {v | v ∈ T ∧ v ≠ z ∧ v ≠ x ∧ J.Adj v x}
  have hmenger : HasDisjointPaths K₀ A₀ B₀ ℓ := by
    refine Menger.exists_disjointPaths K₀ A₀ B₀ (Finite.of_fintype W) ℓ fun U₀ hU₀ => ?_
    let X : Finset W := U₀.toFinset.filter (fun y => y ∈ T ∧ y ≠ z ∧ y ≠ x)
    have hX_sub : (X : Set W) ⊆ T \ {z, x} := by
      intro y hy
      simp only [X, Finset.mem_coe, Finset.mem_filter] at hy
      exact ⟨hy.2.1, by simp [hy.2.2.1, hy.2.2.2]⟩
    have hX_sep : IsSeparator J T z x X := by
      refine ⟨hX_sub, fun ⟨w, hw⟩ => ?_⟩
      let p := w.bypass
      have hp_path : p.IsPath := w.bypass_isPath
      have hp_supp : ∀ y ∈ p.support, y ∈ T \ X :=
        fun y hy => hw y (w.support_bypass_subset_support hy)
      cases hp_eq : p with
      | nil => exact hzx rfl
      | @cons _ a _ hadj₁ rest =>
        have hnd : (z :: rest.support).Nodup := by
          rw [← Walk.support_cons hadj₁, ← hp_eq]
          exact hp_path.support_nodup
        have hz_rest : z ∉ rest.support := (List.nodup_cons.mp hnd).1
        have hsupp_rest : ∀ y ∈ rest.support, y ∈ T \ X := by
          intro y hy
          apply hp_supp
          rw [hp_eq, Walk.support_cons]
          exact List.mem_cons_of_mem _ hy
        have hax : a ≠ x := fun h => hadj_zx (h ▸ hadj₁)
        have haz : a ≠ z := (J.ne_of_adj hadj₁).symm
        have ha_TX : a ∈ T \ X := hsupp_rest a (Walk.start_mem_support _)
        obtain ⟨b, hbT, hbz, hbx, hadj_bx, w₀, hw₀⟩ :=
          exists_innerWalk_of_walk rest rfl hz_rest hsupp_rest hax
        let P₀ : PathFromTo K₀ A₀ B₀ :=
          ⟨a, b, w₀.bypass, w₀.bypass_isPath, ⟨ha_TX.1, haz, hax, hadj₁⟩, ⟨hbT, hbz, hbx, hadj_bx⟩⟩
        obtain ⟨y, hy_supp, hy_U₀⟩ := hU₀ P₀
        have hy_w₀ : y ∈ w₀.support := w₀.support_bypass_subset_support hy_supp
        have hy_props := mem_of_mem_support_innerWalk ⟨ha_TX.1, haz, hax⟩ w₀ y hy_w₀
        have hy_X : y ∈ X := by
          simp only [X, Finset.mem_filter, Set.mem_toFinset]
          exact ⟨hy_U₀, hy_props⟩
        exact hw₀ y hy_w₀ hy_X
    have hle_card : ℓ ≤ X.card := le_card_separator_of_isFlow hzT hxT hf hval hX_sep
    have hcard_le : X.card ≤ U₀.ncard := by
      rw [Set.ncard_eq_toFinset_card']
      exact Finset.card_filter_le _ _
    omega
  rcases hmenger with ⟨P₀, hP₀_disj⟩
  let P : Fin ℓ → J.Walk z x := fun i =>
    Walk.cons (P₀ i).first_mem.2.2.2
      (((P₀ i).walk.map (innerHom J T z x)).concat (P₀ i).last_mem.2.2.2)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i
    have hfirst := (P₀ i).first_mem
    have hmem_w : ∀ y ∈ (P₀ i).walk.support, y ∈ T ∧ y ≠ z ∧ y ≠ x :=
      mem_of_mem_support_innerWalk ⟨hfirst.1, hfirst.2.1, hfirst.2.2.1⟩ (P₀ i).walk
    have hmap_path : ((P₀ i).walk.map (innerHom J T z x)).IsPath := by
      rw [Walk.isPath_def, Walk.support_map]
      exact (P₀ i).isPath.support_nodup.map (fun _ _ h => h)
    have hx_not : x ∉ ((P₀ i).walk.map (innerHom J T z x)).support := by
      intro hx
      rw [Walk.support_map, List.mem_map] at hx
      rcases hx with ⟨y, hy, hyx⟩
      exact (hmem_w y hy).2.2 hyx
    have hconcat_path : (((P₀ i).walk.map (innerHom J T z x)).concat (P₀ i).last_mem.2.2.2).IsPath :=
      hmap_path.concat hx_not (P₀ i).last_mem.2.2.2
    have hz_not :
        z ∉ (((P₀ i).walk.map (innerHom J T z x)).concat (P₀ i).last_mem.2.2.2).support := by
      intro hz
      rw [Walk.support_concat, List.mem_append, List.mem_singleton, Walk.support_map,
        List.mem_map] at hz
      rcases hz with ⟨y, hy, hyz⟩ | hzx'
      · exact (hmem_w y hy).2.1 hyz
      · exact hzx hzx'
    exact Walk.IsPath.cons hconcat_path hz_not
  · intro i y hy
    have hfirst := (P₀ i).first_mem
    have hmem_w : ∀ w ∈ (P₀ i).walk.support, w ∈ T ∧ w ≠ z ∧ w ≠ x :=
      mem_of_mem_support_innerWalk ⟨hfirst.1, hfirst.2.1, hfirst.2.2.1⟩ (P₀ i).walk
    simp only [P, Walk.support_cons, Walk.support_concat, Walk.support_map, List.mem_cons,
      List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | ⟨w, hw, rfl⟩ | rfl
    · exact hzT
    · exact (hmem_w w hw).1
    · exact hxT
  · intro i j hij y hyi hyj
    simp only [P, Walk.support_cons, Walk.support_concat, Walk.support_map, List.mem_cons,
      List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hyi hyj
    rcases hyi with hyz | ⟨wi, hwi, hwi_eq⟩ | hyx
    · exact Or.inl hyz
    · rcases hyj with hyz | ⟨wj, hwj, hwj_eq⟩ | hyx
      · exact Or.inl hyz
      · have hwi_wj : wi = wj := hwi_eq.trans hwj_eq.symm
        subst wj
        exact False.elim (Set.disjoint_left.mp (hP₀_disj hij) hwi hwj)
      · exact Or.inr hyx
    · exact Or.inr hyx

/-! ### Part 4: The extracted cut of a failed search (`Sec21CutStatement` and `Sec22Statement`) -/

/-- If `v ∉ T`, no residual arc leaves `(v, true)`. -/
private theorem not_resAdj_true_of_not_mem {J : SimpleGraph W} {T : Set W} {z x v : W} {k : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f)
    (hvT : v ∉ T) (b : W × Bool) :
    ¬ ResAdj (splitCap J T z x k) f (v, true) b := by
  have hcap_out : splitCap J T z x k (v, true) b = 0 := by
    rcases b with ⟨w, _ | _⟩ <;> simp [splitCap, hvT]
  have hcap_in : splitCap J T z x k b (v, true) = 0 := by
    rcases b with ⟨w, _ | _⟩
    · by_cases h : w = v ∧ w ∈ T
      · exact False.elim (hvT (h.1 ▸ h.2))
      · simp [splitCap, h]
    · simp [splitCap]
  have hle_in := hf.1 b (v, true)
  unfold ResAdj
  omega

/-- If `v ∉ T`, `(v, true)` cannot reach `(x, false)` in the residual graph. -/
private theorem mem_sinkCut_true_of_not_mem {J : SimpleGraph W} {T : Set W} {z x v : W} {k : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f) (hvT : v ∉ T) :
    (v, true) ∈ sinkCut (splitCap J T z x k) f (x, false) := by
  intro hreach
  cases hreach using Relation.ReflTransGen.head_induction_on with
  | @head _ b hab _ _ => exact not_resAdj_true_of_not_mem hf hvT b hab

open Classical in
/-- In a failed flow of value `ℓ ≤ k`, no arc of capacity `> k` crosses the residual sink cut. -/
private theorem splitCap_le_of_mem_sinkCut {J : SimpleGraph W} {T : Set W} {z x : W} {k ℓ : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hℓ : ℓ ≤ k)
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f)
    (hval : flowValue (z, true) f = ℓ)
    (hfail : ¬ ResReach (splitCap J T z x k) f (z, true) (x, false))
    {a b : W × Bool}
    (ha : a ∈ sinkCut (splitCap J T z x k) f (x, false))
    (hb : b ∉ sinkCut (splitCap J T z x k) f (x, false)) :
    splitCap J T z x k a b ≤ k := by
  let W_fin : Finset (W × Bool) := (sinkCut (splitCap J T z x k) f (x, false)).toFinset
  have hzW : (z, true) ∈ W_fin := Set.mem_toFinset.mpr hfail
  have hxW : (x, false) ∉ W_fin := by
    rw [Set.mem_toFinset]
    intro hx
    exact hx Relation.ReflTransGen.refl
  have hno : ∀ u ∈ W_fin, ∀ v ∈ W_finᶜ, ¬ ResAdj (splitCap J T z x k) f u v := by
    intro u hu v hv
    rw [Set.mem_toFinset] at hu
    rw [Finset.mem_compl, Set.mem_toFinset] at hv
    exact not_resAdj_of_mem_sinkCut hu hv
  have heq := flowValue_eq_cutCap_of_no_resAdj hf W_fin hzW hxW hno
  rw [hval] at heq
  have haW : a ∈ W_fin := Set.mem_toFinset.mpr ha
  have hbW : b ∈ W_finᶜ := Finset.mem_compl.mpr (Set.mem_toFinset.not.mpr hb)
  have hle_b :
      (splitCap J T z x k a b : ℤ) ≤ ∑ b' ∈ W_finᶜ, (splitCap J T z x k a b' : ℤ) :=
    Finset.single_le_sum (f := fun b' => (splitCap J T z x k a b' : ℤ))
      (fun _ _ => by positivity) hbW
  have hle_a :
      (∑ b' ∈ W_finᶜ, (splitCap J T z x k a b' : ℤ)) ≤
        ∑ a' ∈ W_fin, ∑ b' ∈ W_finᶜ, (splitCap J T z x k a' b' : ℤ) :=
    Finset.single_le_sum (f := fun a' => ∑ b' ∈ W_finᶜ, (splitCap J T z x k a' b' : ℤ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) haW
  omega

/-- Every vertex of `extractCut J T z x k f` belongs to `T \ {z, x}`. -/
private theorem extractCut_subset {J : SimpleGraph W} {T : Set W} {z x : W} {k ℓ : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hℓ : ℓ ≤ k)
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f)
    (hval : flowValue (z, true) f = ℓ)
    (hfail : ¬ ResReach (splitCap J T z x k) f (z, true) (x, false)) :
    (extractCut J T z x k f : Set W) ⊆ T \ {z, x} := by
  intro v hv
  simp only [extractCut, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have hvT : v ∈ T := by
    by_contra hnotT
    exact hv.2 (mem_sinkCut_true_of_not_mem hf hnotT)
  have hcap_le := splitCap_le_of_mem_sinkCut hℓ hf hval hfail hv.1 hv.2
  have hvz : v ≠ z := by
    rintro rfl
    dsimp [splitCap] at hcap_le
    simp only [true_and, hvT, true_or, ↓reduceIte] at hcap_le
    omega
  have hvx : v ≠ x := by
    rintro rfl
    dsimp [splitCap] at hcap_le
    simp only [true_and, hvT, or_true, ↓reduceIte] at hcap_le
    omega
  exact ⟨hvT, by simp [hvz, hvx]⟩

/-- Propagation of `sinkCut` along an edge `J.Adj u v` inside `T` avoiding `extractCut`. -/
private theorem mem_sinkCut_of_adj {J : SimpleGraph W} {T : Set W} {z x : W} {k ℓ : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hℓ : ℓ ≤ k)
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f)
    (hval : flowValue (z, true) f = ℓ)
    (hfail : ¬ ResReach (splitCap J T z x k) f (z, true) (x, false))
    {u v : W} (huT : u ∈ T) (hvT : v ∈ T) (hadj : J.Adj u v)
    (hu_out : (u, true) ∈ sinkCut (splitCap J T z x k) f (x, false)) :
    (v, false) ∈ sinkCut (splitCap J T z x k) f (x, false) ∧
      (v ∉ extractCut J T z x k f → (v, true) ∈ sinkCut (splitCap J T z x k) f (x, false)) := by
  have hv_in : (v, false) ∈ sinkCut (splitCap J T z x k) f (x, false) := by
    by_contra hv_not
    have hcap_le := splitCap_le_of_mem_sinkCut hℓ hf hval hfail hu_out hv_not
    dsimp [splitCap] at hcap_le
    simp only [huT, hvT, hadj, and_self, ↓reduceIte] at hcap_le
    omega
  refine ⟨hv_in, fun hv_not_cut => ?_⟩
  by_contra hv_out_not
  have hv_cut : v ∈ extractCut J T z x k f := by
    simp only [extractCut, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv_in, hv_out_not⟩
  exact hv_not_cut hv_cut

/-- Propagation of `sinkCut` along any walk in `J` inside `T \ extractCut J T z x k f`. -/
private theorem not_reachIn_of_mem_sinkCut {J : SimpleGraph W} {T : Set W} {z x : W} {k ℓ : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hℓ : ℓ ≤ k)
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f)
    (hval : flowValue (z, true) f = ℓ)
    (hfail : ¬ ResReach (splitCap J T z x k) f (z, true) (x, false))
    {y : W} (hyx : y ≠ x)
    (hy_out : (y, true) ∈ sinkCut (splitCap J T z x k) f (x, false)) :
    ¬ ReachIn J (T \ extractCut J T z x k f) y x := by
  rintro ⟨p, hp⟩
  have hwalk :
      ∀ {u w : W} (q : J.Walk u w),
        (∀ v ∈ q.support, v ∈ T \ extractCut J T z x k f) →
        (u, true) ∈ sinkCut (splitCap J T z x k) f (x, false) →
        (w, true) ∈ sinkCut (splitCap J T z x k) f (x, false) ∧
          (u ≠ w → (w, false) ∈ sinkCut (splitCap J T z x k) f (x, false)) := by
    intro u w q
    induction q with
    | nil =>
      intro _ hu_out
      exact ⟨hu_out, fun hne => False.elim (hne rfl)⟩
    | @cons u v w hadj rest ih =>
      intro hsupp hu_out
      have hu_T : u ∈ T := (hsupp u (Walk.start_mem_support _)).1
      have hv_TX : v ∈ T \ extractCut J T z x k f :=
        hsupp v (List.mem_cons_of_mem _ (Walk.start_mem_support _))
      obtain ⟨hv_in, hv_out_imp⟩ :=
        mem_sinkCut_of_adj hℓ hf hval hfail hu_T hv_TX.1 hadj hu_out
      have hv_out := hv_out_imp hv_TX.2
      have hsupp_rest : ∀ a ∈ rest.support, a ∈ T \ extractCut J T z x k f :=
        fun a ha => hsupp a (List.mem_cons_of_mem _ ha)
      obtain ⟨hw_out, hw_in_imp⟩ := ih hsupp_rest hv_out
      refine ⟨hw_out, fun _ => ?_⟩
      by_cases hvw : v = w
      · exact hvw ▸ hv_in
      · exact hw_in_imp hvw
  have hx_in := (hwalk p hp hy_out).2 hyx
  exact hx_in Relation.ReflTransGen.refl

/-- Every arc crossing `sinkCut` has capacity `1` if it is `(v, false) → (v, true)` for
`v ∈ extractCut`, and `0` otherwise. -/
private theorem splitCap_sinkCut_eq {J : SimpleGraph W} {T : Set W} {z x : W} {k ℓ : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hℓ : ℓ ≤ k)
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f)
    (hval : flowValue (z, true) f = ℓ)
    (hfail : ¬ ResReach (splitCap J T z x k) f (z, true) (x, false))
    {a b : W × Bool}
    (ha : a ∈ sinkCut (splitCap J T z x k) f (x, false))
    (hb : b ∉ sinkCut (splitCap J T z x k) f (x, false)) :
    splitCap J T z x k a b =
      if ∃ v ∈ extractCut J T z x k f, a = (v, false) ∧ b = (v, true) then 1 else 0 := by
  have hcap_le := splitCap_le_of_mem_sinkCut hℓ hf hval hfail ha hb
  have hsub := extractCut_subset hℓ hf hval hfail
  rcases a with ⟨u, _ | _⟩ <;> rcases b with ⟨v, _ | _⟩
  · simp [splitCap]
  · dsimp [splitCap]
    by_cases huv : u = v
    · subst huv
      have hu_cut : u ∈ extractCut J T z x k f := by
        simp only [extractCut, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ha, hb⟩
      have hu_sub := hsub hu_cut
      have huT : u ∈ T := hu_sub.1
      have huz : u ≠ z := fun h => hu_sub.2 (by simp [h])
      have hux : u ≠ x := fun h => hu_sub.2 (by simp [h])
      simp [hu_cut, huT, huz, hux]
    · simp [huv]
  · have hnot_adj : ¬ (u ∈ T ∧ v ∈ T ∧ J.Adj u v) := by
      intro hadj
      dsimp [splitCap] at hcap_le
      simp only [hadj, and_self, ↓reduceIte] at hcap_le
      omega
    simp [splitCap, hnot_adj]
  · simp [splitCap]

open Classical in
/-- The cardinality of `extractCut J T z x k f` equals `ℓ`. -/
private theorem card_extractCut_eq {J : SimpleGraph W} {T : Set W} {z x : W} {k ℓ : ℕ}
    {f : W × Bool → W × Bool → ℕ}
    (hℓ : ℓ ≤ k)
    (hf : IsFlow (splitCap J T z x k) (z, true) (x, false) f)
    (hval : flowValue (z, true) f = ℓ)
    (hfail : ¬ ResReach (splitCap J T z x k) f (z, true) (x, false)) :
    (extractCut J T z x k f).card = ℓ := by
  let W_fin : Finset (W × Bool) := (sinkCut (splitCap J T z x k) f (x, false)).toFinset
  let X := extractCut J T z x k f
  have hzW : (z, true) ∈ W_fin := Set.mem_toFinset.mpr hfail
  have hxW : (x, false) ∉ W_fin := by
    rw [Set.mem_toFinset]
    intro hx
    exact hx Relation.ReflTransGen.refl
  have hno : ∀ u ∈ W_fin, ∀ v ∈ W_finᶜ, ¬ ResAdj (splitCap J T z x k) f u v := by
    intro u hu v hv
    rw [Set.mem_toFinset] at hu
    rw [Finset.mem_compl, Set.mem_toFinset] at hv
    exact not_resAdj_of_mem_sinkCut hu hv
  have heq := flowValue_eq_cutCap_of_no_resAdj hf W_fin hzW hxW hno
  rw [hval] at heq
  have h1 :
      (∑ a ∈ W_fin, ∑ b ∈ W_finᶜ, (splitCap J T z x k a b : ℤ)) =
        ∑ a ∈ W_fin, ∑ b ∈ W_finᶜ, if ∃ v ∈ X, a = (v, false) ∧ b = (v, true) then (1 : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [Set.mem_toFinset] at ha
    rw [Finset.mem_compl, Set.mem_toFinset] at hb
    rw [splitCap_sinkCut_eq hℓ hf hval hfail ha hb]
    split_ifs <;> rfl
  have h2 : ∀ v ∈ X, (v, false) ∈ W_fin ∧ (v, true) ∈ W_finᶜ := by
    intro v hvX
    simp only [X, extractCut, Finset.mem_filter, Finset.mem_univ, true_and] at hvX
    exact ⟨Set.mem_toFinset.mpr hvX.1, Finset.mem_compl.mpr (Set.mem_toFinset.not.mpr hvX.2)⟩
  have h3 :
      (∑ a ∈ W_fin, ∑ b ∈ W_finᶜ, if ∃ v ∈ X, a = (v, false) ∧ b = (v, true) then (1 : ℤ) else 0) =
        ∑ v ∈ X, (1 : ℤ) := by
    trans (∑ a ∈ X.image (fun v => (v, false)),
      ∑ b ∈ W_finᶜ, if ∃ v ∈ X, a = (v, false) ∧ b = (v, true) then (1 : ℤ) else 0)
    · refine (Finset.sum_subset (fun a ha => ?_) (fun a _ ha_not => ?_)).symm
      · simp only [Finset.mem_image] at ha
        rcases ha with ⟨v, hvX, rfl⟩
        exact (h2 v hvX).1
      · refine Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right_iff]
        rintro ⟨v, hvX, rfl, rfl⟩
        exact False.elim (ha_not (Finset.mem_image_of_mem _ hvX))
    · rw [Finset.sum_image (fun u _ v _ h => by injection h)]
      refine Finset.sum_congr rfl fun v hvX => ?_
      rw [Finset.sum_eq_single (v, true)]
      · simp [hvX]
      · intro b _ hne
        rw [ite_eq_right_iff]
        rintro ⟨w, _, h1, h2⟩
        cases h1
        exact False.elim (hne h2)
      · intro h
        exact False.elim (h (h2 v hvX).2)
  rw [h1, h3, Finset.sum_const, nsmul_eq_mul, mul_one] at heq
  exact_mod_cast heq.symm

/-- **The cut of a failed computation** (Section 2.1): after an unsuccessful search, the extracted
set is a minimum `z`-`x` separator of size the value of the flow. -/
theorem sec21Cut_proved : Sec21CutStatement := by
  intro W _ _ J T z x k ℓ f hzT hxT hzx _ hℓ hf hval hfail
  have hcard : (extractCut J T z x k f).card = ℓ :=
    card_extractCut_eq hℓ hf hval hfail
  have hsep : IsSeparator J T z x (extractCut J T z x k f) :=
    ⟨extractCut_subset hℓ hf hval hfail,
      not_reachIn_of_mem_sinkCut hℓ hf hval hfail hzx hfail⟩
  refine ⟨⟨hsep, fun X' hsep' => ?_⟩, hcard⟩
  rw [hcard]
  exact le_card_separator_of_isFlow hzT hxT hf hval hsep'

/-- **The cut with largest source side** (Section 2.2): the extracted separator has open source
side containing that of every minimum `z`-`x` vertex separator. -/
theorem sec22_proved : Sec22Statement := by
  intro W _ _ J T z x k ℓ f hzT hxT hzx hadj_zx hℓ hf hval hfail
  obtain ⟨hmin, hcard⟩ := sec21Cut_proved J T z x k ℓ f hzT hxT hzx hadj_zx hℓ hf hval hfail
  refine ⟨hmin, fun X' hmin' y hy => ?_⟩
  have hcard' : X'.card = ℓ := by
    have h1 := hmin.2 X' hmin'.1
    have h2 := hmin'.2 (extractCut J T z x k f) hmin.1
    omega
  let C' := sepCut J T x X'
  have hzC' : (z, true) ∈ C' := by
    rw [mem_sepCut_true]
    exact ⟨hzT, fun hzX => (hmin'.1.1 hzX).2 (by simp), hmin'.1.2⟩
  have hxC' : (x, false) ∉ C' := by
    rw [mem_sepCut_false]
    rintro (hxU | hxX)
    · exact hxU.2.2 (ReachIn.refl ⟨hxT, hxU.2.1⟩)
    · exact (hmin'.1.1 hxX).2 (by simp)
  have heq_cap :
      flowValue (z, true) f = ∑ a ∈ C', ∑ b ∈ C'ᶜ, (splitCap J T z x k a b : ℤ) := by
    rw [hval, sum_splitCap_sepCut k hmin'.1, hcard']
  have hno_res := no_resAdj_of_flowValue_eq_cutCap hf C' hzC' hxC' heq_cap
  have hyC' : (y, true) ∈ C' := mem_sepCut_true.mpr hy
  have hy_sink : (y, true) ∈ sinkCut (splitCap J T z x k) f (x, false) :=
    not_resReach_of_no_resAdj C' hno_res hyC' hxC'
  have hyx : y ≠ x := by
    rintro rfl
    exact hy.2.2 (ReachIn.refl ⟨hxT, hy.2.1⟩)
  refine ⟨hy.1, ?_, not_reachIn_of_mem_sinkCut hℓ hf hval hfail hyx hy_sink⟩
  intro hy_cut
  simp only [extractCut, Finset.mem_filter, Finset.mem_univ, true_and] at hy_cut
  exact hy_cut.2 hy_sink

end GraphMinor.Crossing

