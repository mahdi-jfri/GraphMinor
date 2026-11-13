module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM19.Defs2
import GraphMinor.GM21.CuffSpaces
import GraphMinor.GM19.Section4c
import GraphMinor.GM19.CapModel
import GraphMinor.Surface.Classification
import GraphMinor.Surface.ModelCriterion
import GraphMinor.Surface.NormalWord

/-!
# Graph Minors XXI, (6.3): the measure of the induction

The proof of (6.3) (page 28 of the preprint) goes "by induction on $\Sigma$". Its inductive
hypothesis (1) asks for one bound `λ(p, q, r)` that works for every surface `Σ'` with `Σ̂'` simpler
than `Σ̂`, or with `Σ̂' ≅ Σ̂` and fewer cuffs. This file makes that induction precise.

A connected surface `Σ` is homeomorphic to a model `Σ(a, b, c)`. We say that `Σ` *has type*
`(2a + b, c)`. By the model criterion the type does not depend on the model
(`HasType.unique`). The capped surface `Σ̂` has type `(2a + b, 0)` (`HasType.cap`), and *simpler*
lowers the first number (`HasType.lt_of_isSimplerThan`). So the paper's induction is an induction
on the type, in lexicographic order.

There are infinitely many types below a given one, since the number of cuffs is not bounded. A
surface with a presentation of defect `≤ r` has at most `r` cuffs (`ncard_cuffs_le`), because each
cuff has a vertex of `Γ` and each support lies in one cuff. So only finitely many types matter for
a given defect, and one bound works for all of them (`exists_uniform_bound`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Induction

open Set Function Topology GraphMinor.Surface

universe u v w

/-! ## The number of cuffs is at most the defect -/

section Cuffs

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
  {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

/-- Two cuffs that meet are equal. -/
theorem eq_of_mem_cuffs_of_mem {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) {x : S}
    (hx : x ∈ C) (hx' : x ∈ C') : C = C' := by
  obtain ⟨y, -, rfl⟩ := hC
  obtain ⟨y', -, rfl⟩ := hC'
  rw [connectedComponentIn_eq hx, connectedComponentIn_eq hx']

/-- A surface with a presentation of defect `r` has at most `r` cuffs. Every cuff has a vertex of
`Γ` (it has two, by the definition of a presentation), this vertex lies in a support, and a support
is connected, so it lies in one cuff. -/
theorem ncard_cuffs_le (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    (cuffs S).ncard ≤ r := by
  classical
  have hvert : ∀ C ∈ cuffs S, ∃ j : Fin r, (F_star j ∩ C).Nonempty := by
    intro C hC
    have h2 := hP.cuff_vertices_ge_two C hC
    obtain ⟨v, hv⟩ := nonempty_of_ncard_ne_zero (by omega : (Γ.V ∩ C).ncard ≠ 0)
    have hvbd : v ∈ bd S := by
      obtain ⟨y, hy, rfl⟩ := hC
      exact connectedComponentIn_subset _ _ hv.2
    have hcov := hP.bd_vertices_covered ⟨hv.1, hvbd⟩
    rw [mem_iUnion] at hcov
    obtain ⟨j, hj⟩ := hcov
    exact ⟨j, v, hj, hv.2⟩
  let g : cuffs S → Fin r := fun C => (hvert C.1 C.2).choose
  have hinj : Injective g := by
    rintro ⟨C, hC⟩ ⟨C', hC'⟩ hgg
    have h1 := (hvert C hC).choose_spec
    have h2 := (hvert C' hC').choose_spec
    simp only [g] at hgg
    rw [hgg] at h1
    obtain ⟨x, hxF, hxC⟩ := h1
    obtain ⟨x', hxF', hxC'⟩ := h2
    obtain ⟨D, hD, hFD, -⟩ :=
      exists_cuff_of_isSupportOfDrawing (hP.supports_isSupport (hvert C' hC').choose)
    exact Subtype.ext ((eq_of_mem_cuffs_of_mem hC hD hxC (hFD hxF)).trans
      (eq_of_mem_cuffs_of_mem hC' hD hxC' (hFD hxF')).symm)
  have := Nat.card_le_card_of_injective g hinj
  rwa [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fin] at this

end Cuffs

/-! ## The type of a surface -/

/-- `S` has type `(n, c)`: it is homeomorphic to a model `Σ(a, b, c)` with `2a + b = n`. The number
`2a + b` is the Euler genus of `Σ̂`, and `c` is the number of cuffs. -/
def HasType (S : Type) [TopologicalSpace S] (n c : ℕ) : Prop :=
  ∃ a b : ℕ, 2 * a + b = n ∧ Nonempty (S ≃ₜ SurfaceModel a b c)

/-- The number of cuffs of the model `Σ(a, b, c)` is `c`. -/
theorem ncard_cuffs_model (a b c : ℕ) : (cuffs (SurfaceModel a b c)).ncard = c := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  let := ht
  exact ncard_cuffs hf

/-- Every connected surface has a type. -/
theorem exists_hasType {S : Type} [TopologicalSpace S] (hS : IsSurface S) [ConnectedSpace S] :
    ∃ n c, HasType S n c := by
  obtain ⟨a, b, c, e⟩ := classification S hS inferInstance
  exact ⟨2 * a + b, c, a, b, rfl, e⟩

/-- The second number of the type is the number of cuffs. -/
theorem HasType.ncard_cuffs {S : Type} [TopologicalSpace S] {n c : ℕ} (h : HasType S n c) :
    (cuffs S).ncard = c := by
  obtain ⟨a, b, -, ⟨e⟩⟩ := h
  rw [ncard_cuffs_congr e, ncard_cuffs_model]

/-- The type does not depend on the model, by the model criterion. -/
theorem HasType.unique {S : Type} [TopologicalSpace S] {n c n' c' : ℕ} (h : HasType S n c)
    (h' : HasType S n' c') : n = n' ∧ c = c' := by
  obtain ⟨a, b, rfl, ⟨e⟩⟩ := h
  obtain ⟨a', b', rfl, ⟨e'⟩⟩ := h'
  obtain ⟨hc, hn, -⟩ := (modelCriterion.2 a b c a' b' c').mp ⟨e.symm.trans e'⟩
  exact ⟨hn, hc⟩

/-- The type moves along a homeomorphism. -/
theorem HasType.congr {S T : Type} [TopologicalSpace S] [TopologicalSpace T] {n c : ℕ}
    (h : HasType S n c) (e : T ≃ₜ S) : HasType T n c := by
  obtain ⟨a, b, hn, ⟨e'⟩⟩ := h
  exact ⟨a, b, hn, ⟨e.trans e'⟩⟩

/-- If `Σ` has type `(n, c)`, then `Σ̂` has type `(n, 0)`: pasting discs on the cuffs of
`Σ(a, b, c)` gives `Σ(a, b, 0)` (`capModel`). -/
theorem HasType.cap {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] {n c : ℕ}
    (h : HasType S n c) (cap : GM19.IsCappedSurface S Shat) : HasType Shat n 0 := by
  obtain ⟨a, b, hn, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := GM19.capModel a b c Shat (cap.ofHomeo e.symm)
  exact ⟨a, b, hn, ⟨e'⟩⟩

/-- A closed surface simpler than another has a smaller Euler genus. -/
theorem HasType.lt_of_isSimplerThan {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {n m : ℕ} (hX : HasType X n 0) (hY : HasType Y m 0) (h : IsSimplerThan X Y) : n < m := by
  obtain ⟨a, b, c, a', b', c', ⟨eX⟩, ⟨eY⟩, -, -, hlt⟩ := h
  obtain ⟨hn, hc⟩ := hX.unique ⟨a, b, rfl, ⟨eX⟩⟩
  obtain ⟨hm, hc'⟩ := hY.unique ⟨a', b', rfl, ⟨eY⟩⟩
  omega

/-- Homeomorphic surfaces have the same type. -/
theorem HasType.eq_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {n c m d : ℕ} (hX : HasType X n c) (hY : HasType Y m d) (e : X ≃ₜ Y) : n = m ∧ c = d :=
  hX.unique (hY.congr e)

/-! ## One bound for all smaller types -/

/-- The statement proved for each type `(n, c)` in the induction for (6.3): for all `p, r ≥ 0` and
`q ≥ 1` there is one bound `λ` for the number of `Σ`-jumps, valid for every surface `Σ` of type
`(n, c)`. -/
def BoundForType (n c : ℕ) : Prop :=
  ∀ (p r q : ℕ), 1 ≤ q →
    ∃ lam : ℕ,
      ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S], IsSurface S → HasType S n c →
        ∀ {α : Type u} {β : Type v}
          (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
          (ιV : S → α) (ιE : Set S → β)
          (r' : ℕ) (F_star : Fin r' → Set S) (H : Fin r' → Hypergraph α β)
          (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
          G.IsGraph →
          r' ≤ r →
          PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
          IsExhaustiveLinkage G Γ_sub r' H L →
          IsPLinkage G L p →
          (sigmaJumps Γ Γ_sub ιV).encard ≤ lam

/-- The order of the induction: `(n', c')` comes before `(n, c)` if `n' < n`, or `n' = n` and
`c' < c`. -/
def TypeLt (n' c' n c : ℕ) : Prop := n' < n ∨ (n' = n ∧ c' < c)

/-- A bound for each member of a finite set gives one bound for all of them, if bounds can be
raised. -/
theorem exists_bound_of_finset {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (hmono : ∀ i l l', P i l → l ≤ l' → P i l') (h : ∀ i ∈ s, ∃ l, P i l) :
    ∃ l, ∀ i ∈ s, P i l := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨l₁, hl₁⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨l₂, hl₂⟩ := h i (Finset.mem_insert_self _ _)
    refine ⟨max l₁ l₂, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hmono _ _ _ hl₂ (le_max_right _ _)
    · exact hmono _ _ _ (hl₁ j hj) (le_max_left _ _)

/-- One bound `λ` for the number of `Σ'`-jumps, for every surface `Σ'` whose type comes before
`(n, c)`, every presentation of depth `≤ q` and defect `≤ r`, and every exhaustive vital
`p`-linkage. This is the form of the inductive hypothesis (1) of the proof of (6.3). -/
def BoundBelow (n c p q r lam : ℕ) : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ n' c', HasType S n' c' → TypeLt n' c' n c →
    ∀ {α : Type u} {β : Type v}
      (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
      (ιV : S → α) (ιE : Set S → β)
      (r' : ℕ) (F_star : Fin r' → Set S) (H : Fin r' → Hypergraph α β)
      (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
      G.IsGraph →
      r' ≤ r →
      PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
      IsExhaustiveLinkage G Γ_sub r' H L →
      IsPLinkage G L p →
      (sigmaJumps Γ Γ_sub ιV).encard ≤ lam

/-- The inductive hypothesis (1) of the proof of (6.3), from the statement for each smaller type:
for all `p, r ≥ 0` and `q ≥ 1` one bound `λ(p, q, r)` works for every surface whose type comes
before `(n, c)`. Only types with at most `r` cuffs matter (`ncard_cuffs_le`), and there are finitely
many of them. -/
theorem exists_uniform_bound {n c : ℕ}
    (ih : ∀ n' c', TypeLt n' c' n c → BoundForType.{u, v} n' c') (p r q : ℕ) (hq : 1 ≤ q) :
    ∃ lam : ℕ, BoundBelow.{u, v} n c p q r lam := by
  classical
  let P : ℕ × ℕ → ℕ → Prop := fun x lam =>
    TypeLt x.1 x.2 n c →
      ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S], IsSurface S → HasType S x.1 x.2 →
        ∀ {α : Type u} {β : Type v}
          (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
          (ιV : S → α) (ιE : Set S → β)
          (r' : ℕ) (F_star : Fin r' → Set S) (H : Fin r' → Hypergraph α β)
          (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
          G.IsGraph →
          r' ≤ r →
          PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
          IsExhaustiveLinkage G Γ_sub r' H L →
          IsPLinkage G L p →
          (sigmaJumps Γ Γ_sub ιV).encard ≤ lam
  have hmono : ∀ x l l', P x l → l ≤ l' → P x l' := by
    intro x l l' hP hll' hlt S _ _ hS hT α β G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp
    exact (hP hlt S hS hT G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp).trans
      (by exact_mod_cast hll')
  obtain ⟨lam, hlam⟩ := exists_bound_of_finset (Finset.range (n + 1) ×ˢ Finset.range (r + 1)) P
    hmono (fun x _ => by
      by_cases hlt : TypeLt x.1 x.2 n c
      · obtain ⟨l, hl⟩ := ih x.1 x.2 hlt p r q hq
        exact ⟨l, fun _ S _ _ hS hT => hl S hS hT⟩
      · exact ⟨0, fun h => absurd h hlt⟩)
  refine ⟨lam, ?_⟩
  intro S _ _ hS n' c' hT hlt α β G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp
  have hc' : c' ≤ r := by
    obtain ⟨qf, hP, -, -⟩ := hd
    rw [← hT.ncard_cuffs]
    exact (ncard_cuffs_le hP).trans hr
  have hn' : n' ≤ n := by rcases hlt with h | ⟨h, -⟩ <;> omega
  exact hlam (n', c') (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
    Finset.mem_range.mpr (by omega)⟩) hlt S hS hT G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp

end Induction
end GM21
end GraphMinor
