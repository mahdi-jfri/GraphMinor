module

public import GraphMinor.GM08.Section16Defs
public import GraphMinor.GM08.Section17Defs
public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section17Cylinder
import GraphMinor.GM08.Section17Align
import GraphMinor.GM08.Section17Collar
import GraphMinor.GM08.Section16Conclusion
import GraphMinor.GM08.Section14

/-!
# Graph Minors VIII (17.1)–(17.3)

A tubular graft has a proper drawing in the fixed cylinder. Its cuff
counts add to its index, so it lies in the displayed union. Conversely,
a drawing counted by that union is framed by the cuffs, and its index
is their sum. This proves the class equality (17.1) used to start the
induction in the cylinder case.

(17.2) says that a fixed graft of a fixed-cuff class is simulated in
every member of the class whose framing is linked enough. The work is in
`Section17Collar`. (17.3) then follows by the paper's induction on the
index, from (17.1), (17.2), (4.2) and (16.1).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v

/-- Graph Minors VIII, (17.1), page 284: `ℬ(k)` is the union of the
fixed-cuff classes `ℬ(k₁,k₂)` over all `k₁ + k₂ ≤ k`, in a fixed
cylinder with its two cuffs ordered as `C,D`. -/
theorem theorem_17_1_proof {S : Type} [TopologicalSpace S] (hS : IsCylinder S)
    {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} (k : ℕ) :
    classB (α := α) (β := β) (k : ℤ) =
      ⋃ p ∈ {p : ℕ × ℕ | p.1 + p.2 ≤ k}, classBCuffCounts S C D p.1 p.2 := by
  ext X
  constructor
  · rintro ⟨htub, hk⟩
    obtain ⟨gd⟩ := embedsGraft_cylinder_of_isTubularGraft hS htub
    have hindex := graftDrawing_index_eq_cuff_counts hS hC hD hCD gd
    have hbound : (gd.drawing.V ∩ C).ncard + (gd.drawing.V ∩ D).ncard ≤ k := by
      rw [← hindex]
      exact Int.ofNat_le.mp hk
    exact mem_iUnion₂.mpr ⟨((gd.drawing.V ∩ C).ncard, (gd.drawing.V ∩ D).ncard),
      hbound, gd, rfl, rfl⟩
  · intro hX
    obtain ⟨p, hp, gd, hCcount, hDcount⟩ := mem_iUnion₂.mp hX
    refine ⟨isTubularGraft_of_embedsGraft_cylinder hS ⟨gd⟩, ?_⟩
    have hindex := graftDrawing_index_eq_cuff_counts hS hC hD hCD gd
    rw [hCcount, hDcount] at hindex
    exact Int.ofNat_le.mpr (hindex ▸ hp)

/-- **Graph Minors VIII, (17.2)** (page 284): "*Let* $(H, U) \in \mathscr{B}(k_1, k_2)$.
*Then there are integers* $r, s \ge 0$ *such that for every*
$(G, T) \in \mathscr{B}(k_1, k_2)$, *either* $(H, U)$ *is simulated in* $(G, T)$
*or* $(G, T) \in \mathscr{B}(k_1 + k_2, r, s)$." -/
theorem theorem_17_2_proof {S : Type} [TopologicalSpace S] (hS : IsCylinder S)
    {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} {k₁ k₂ : ℕ} {Y : Graft α β}
    (hY : Y ∈ classBCuffCounts S C D k₁ k₂) :
    ∃ r s : ℕ, ∀ X : Graft α β, X ∈ classBCuffCounts S C D k₁ k₂ →
      IsGraftSimulatedIn Y X ∨ X ∈ printedClassBUnlinked (k₁ + k₂) r s := by
  refine ⟨cylinderMinorThreshold (rootLeafGraft Y) + 1,
    max 4 (2 * cylinderMinorThreshold (rootLeafGraft Y)), fun X hX => ?_⟩
  obtain ⟨DY, DX, hbd, hXC, hXD⟩ :=
    exists_aligned_drawings_of_mem_classBCuffCounts hS hC hD hCD hY hX
  obtain ⟨cap, hcapC, hcapD⟩ := CylinderSphereCap.exists_with_cuffs hS hC hD hCD
  obtain ⟨τ, hτΓ, hτC, hτD, hfr⟩ := exists_tube_framing_with_cuffs hS hC hD hCD DX
  have hindex : X.index = k₁ + k₂ := by
    rw [graftDrawing_index_eq_cuff_counts hS hC hD hCD DX, hXC, hXD]
  by_cases hlink : τ.IsPrintedBoundaryLinked (cylinderMinorThreshold (rootLeafGraft Y) + 1)
      (max 4 (2 * cylinderMinorThreshold (rootLeafGraft Y)))
  · exact .inl (isGraftSimulatedIn_of_printedBoundaryLinked hS cap DY DX hbd τ hτΓ
      (hτC.trans hcapC.symm) (hτD.trans hcapD.symm) hlink)
  · exact .inr ⟨hindex.le, S, inferInstance, τ, hfr, hlink⟩

/-- A union of well-rooted classes over a finite index set is well-rooted,
by (4.2) and induction on the index set. -/
theorem isWellRootedGraftClass_biUnion_finset {α : Type u} {β : Type v} {ι : Type*}
    (s : Finset ι) {𝒜 : ι → Set (Graft α β)} (h : ∀ i ∈ s, IsWellRootedGraftClass (𝒜 i)) :
    IsWellRootedGraftClass (⋃ i ∈ s, 𝒜 i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro X hX
    simpa using hX 0
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact theorem_4_2_proof (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A fixed-cuff class `ℬ(k₁,k₂)` is well-rooted if `ℬ(k₁+k₂-1)` is. This is
the main part of the proof of (17.3), page 284. -/
theorem isWellRootedGraftClass_classBCuffCounts {S : Type} [TopologicalSpace S]
    (hS : IsCylinder S) {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} {k k₁ k₂ : ℕ} (hk : k₁ + k₂ ≤ k)
    (hprev : IsWellRootedGraftClass (classB (α := α) (β := β) ((k : ℤ) - 1))) :
    IsWellRootedGraftClass (classBCuffCounts (α := α) (β := β) S C D k₁ k₂) := by
  intro X hX
  -- if the first graft is simulated in a later one, we are done
  by_cases hfirst : ∃ j, 0 < j ∧ IsGraftSimulatedIn (X 0) (X j)
  · obtain ⟨j, hj, hsim⟩ := hfirst
    exact ⟨0, j, hj, hsim⟩
  push Not at hfirst
  -- otherwise every later graft is in `ℬ(k,r,s)`, by (17.2)
  obtain ⟨r, s, hrs⟩ := theorem_17_2_proof hS hC hD hCD (hX 0)
  have hlater : ∀ n, X (n + 1) ∈ printedClassBUnlinked k r s := by
    intro n
    rcases hrs (X (n + 1)) (hX (n + 1)) with h | ⟨hidx, h⟩
    · exact absurd h (hfirst (n + 1) n.succ_pos)
    · exact ⟨hidx.trans hk, h⟩
  -- and `ℬ(k,r,s)` is well-rooted by (16.1)
  obtain ⟨i, j, hij, hsim⟩ := theorem_16_1_proof k r s hprev (fun n => X (n + 1)) hlater
  exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, hsim⟩

/-- The induction step of (17.3), page 284: if `ℬ(k-1)` is well-rooted then
so is `ℬ(k)`. By (17.1) and (4.2) it is enough that each `ℬ(k₁,k₂)` with
`k₁ + k₂ ≤ k` is well-rooted. -/
theorem isWellRootedGraftClass_classB_of_prev {α : Type u} {β : Type v} (k : ℕ)
    (hprev : IsWellRootedGraftClass (classB (α := α) (β := β) ((k : ℤ) - 1))) :
    IsWellRootedGraftClass (classB (α := α) (β := β) (k : ℤ)) := by
  classical
  -- a fixed cylinder with its two cuffs
  have hS : IsCylinder (SurfaceModel 0 0 2) := ⟨(isSurface_model 0 0 2).1, ⟨Homeomorph.refl _⟩⟩
  obtain ⟨C, D, hCD, hcuffs⟩ := hS.exists_cuffs
  have hC : C ∈ cuffs (SurfaceModel 0 0 2) := hcuffs ▸ mem_insert C {D}
  have hD : D ∈ cuffs (SurfaceModel 0 0 2) := hcuffs ▸ mem_insert_of_mem C rfl
  rw [theorem_17_1_proof hS hC hD hCD k]
  let s : Finset (ℕ × ℕ) :=
    (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p => p.1 + p.2 ≤ k)
  refine isWellRootedGraftClass_mono ?_ (isWellRootedGraftClass_biUnion_finset s
    fun p hp => isWellRootedGraftClass_classBCuffCounts hS hC hD hCD
      (Finset.mem_filter.mp hp).2 hprev)
  intro X hX
  obtain ⟨p, hp, hXp⟩ := mem_iUnion₂.mp hX
  have hp' : p.1 + p.2 ≤ k := hp
  refine mem_iUnion₂.mpr ⟨p, ?_, hXp⟩
  simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- **Graph Minors VIII, (17.3)** (page 284): "*For any integer* $k \ge 0$,
$\mathscr{B}(k)$ *is well-rooted.*" The proof is by induction on `k`, starting
from `ℬ(-1) = ∅`. -/
theorem theorem_17_3_proof {α : Type u} {β : Type v} (k : ℕ) :
    IsWellRootedGraftClass (classB (α := α) (β := β) (k : ℤ)) := by
  induction k with
  | zero =>
    apply isWellRootedGraftClass_classB_of_prev
    intro X hX
    have h := hX 0
    rw [Nat.cast_zero, zero_sub, classB_neg_one] at h
    exact h.elim
  | succ k ih =>
    apply isWellRootedGraftClass_classB_of_prev
    have h : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
    rw [h]
    exact ih

end GraphMinor.GM08
