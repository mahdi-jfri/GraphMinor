module

public import GraphMinor.GM08.Section18Classes
public import GraphMinor.GM08.Section16Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section13
import GraphMinor.GM08.Section17
import GraphMinor.GM08.Section17LeafReflect
import GraphMinor.GM08.Section17RootLeaves
import GraphMinor.GM08.Section18Leaf
import GraphMinor.GM08.Section18ClosedGraft
import GraphMinor.GM08.Section18Drawing
import GraphMinor.GM07.CuffStep
import GraphMinor.GM07.GoodEdge
import GraphMinor.GM07.CutBounds

/-!
# The main step in the proof of (18.3)

This is the claim on page 287: for a connected surface `Σ` with `g(Σ) ≤ h`,
not a sphere, disc or cylinder, every class `𝒞(Σ; k₁, …, k_c)` with
`k₁ + ⋯ + k_c ≤ k` is well-rooted, given the two inductive hypotheses.

The proof uses two facts about a drawing, proved in other files.
- `CutStepStatement`: a graft drawn with a normal schism `F` that misses the
  boundary and has at most `N` vertices lies in `W(𝒞(h', k + 2N + 2))` for
  some `h' < g(Σ)`. The paper gets this by cutting along `F` and using (18.2).
- `SplitStepStatement`: a graft drawn with the O-arc of (18.1)(iv) lies in
  `W(𝒞(Σ, k - 1) ⊕ ℬ(2k - 1))`, up to isomorphism.

Since the remark of VII used in (18.1) is false (see the correction to
(18.1) in `corrections/GM08.md`), we
apply (18.1) to the root-leaf grafts (`theorem_18_1_leaf`). So the class `𝒟`
of the paper holds the root-leaf grafts of the sequence, and a simulation
between two of them gives one between the grafts themselves
(`isGraftSimulatedIn_of_rootLeafGraft`). On a closed surface there are no
roots, and the printed (18.1) is proved (`theorem_18_1_closed`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v w

/-! ## Monotonicity of the class operations -/

theorem WiGraftClass_mono {α : Type u} {β : Type v} {𝒜 ℬ : Set (Graft α β)} (h : 𝒜 ⊆ ℬ) :
    ∀ i, WiGraftClass i 𝒜 ⊆ WiGraftClass i ℬ
  | 0 => h
  | i + 1 => by
    rintro Y ⟨X, hX, hXY⟩
    exact ⟨X, WiGraftClass_mono h i hX, hXY⟩

theorem WGraftClass_mono {α : Type u} {β : Type v} {𝒜 ℬ : Set (Graft α β)} (h : 𝒜 ⊆ ℬ) :
    WGraftClass 𝒜 ⊆ WGraftClass ℬ := by
  intro X hX
  obtain ⟨i, hi⟩ := mem_iUnion.mp hX
  exact mem_iUnion.mpr ⟨i, WiGraftClass_mono h i hi⟩

theorem isoGraftClass_mono {α : Type u} {β : Type v} {𝒜 ℬ : Set (Graft α β)} (h : 𝒜 ⊆ ℬ) :
    isoGraftClass 𝒜 ⊆ isoGraftClass ℬ := by
  rintro X ⟨Y, hY, hi⟩
  exact ⟨Y, h hY, hi⟩

theorem graftDirectSumClass_mono {α : Type u} {β : Type v} {𝒜 𝒜' ℬ ℬ' : Set (Graft α β)}
    (h₁ : 𝒜 ⊆ 𝒜') (h₂ : ℬ ⊆ ℬ') : graftDirectSumClass 𝒜 ℬ ⊆ graftDirectSumClass 𝒜' ℬ' := by
  rintro X ⟨A, hA, B, hB, hs⟩
  exact ⟨A, h₁ hA, B, h₂ hB, hs⟩

/-! ## The two facts used in the step -/

/-- The cut step of (18.3), page 287, case (i): a graft drawn in a connected
surface `Σ`, not a sphere, disc or cylinder, with a normal schism that misses
the boundary and has at most `N` vertices, lies in `W(𝒞(h', k + 2N + 2))`, up to
isomorphism, for some `h' < g(Σ)`. -/
def CutStepStatement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (a b c : ℕ), 3 ≤ 3 * a + 3 * b + c → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ (α β : Type u) [Infinite α] (X : Graft α β) (DX : GraftDrawing X.G X.T S)
      (F : Set S) (N k : ℕ), GM07.IsSchism F → DX.drawing.IsNormal F → F ∩ bd S = ∅ →
      (DX.drawing.V ∩ F).ncard ≤ N → X.index ≤ k →
      ∃ h' < surfaceComplexity S,
        X ∈ WGraftClass (isoGraftClass (classC.{u, u, w} h' (k + 2 * N + 2)))

/-- The split step of (18.3), page 287, case (ii): a graft drawn in a
connected surface `Σ` with a normal O-arc `F` surrounding a cuff `C`, with
`F ∩ bd(Σ) ⊆ C` and fewer vertices on `F` than on `C`, lies in
`W(𝒞(Σ, k - 1)* ⊕ ℬ(2k - 1)*)`. -/
def SplitStepStatement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (a b c : ℕ), 3 ≤ 3 * a + 3 * b + c → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ (α β : Type u) [Infinite α] (X : Graft α β) (DX : GraftDrawing X.G X.T S)
      (C F : Set S) (k : ℕ), C ∈ cuffs S → DX.drawing.IsNormal F → IsOArc F →
      GM07.SurroundsCuff F C → F ∩ bd S ⊆ C →
      (DX.drawing.V ∩ F).ncard < (DX.drawing.V ∩ C).ncard → X.index ≤ k →
      X ∈ WGraftClass (graftDirectSumClass (isoGraftClass (classCSurface S (k - 1)))
        (isoGraftClass (classB (2 * (k : ℤ) - 1))))

/-! ## The step -/

/-- The index of a graft drawing is the number of boundary vertices. -/
theorem GraftDrawing.index_eq {S : Type w} [TopologicalSpace S] [T1Space S]
    {α : Type u} {β : Type v} {X : Graft α β} (gd : GraftDrawing X.G X.T S) :
    X.index = (gd.drawing.V ∩ bd S).ncard :=
  ncard_roots_eq_boundary_vertices gd

/-- The inductive hypotheses of (18.3), in the form used by the step: all
grafts with labels in one universe `u`. -/
def ClassCWellRooted (h k : ℕ) : Prop :=
  ∀ (α β : Type u), IsWellRootedGraftClass (classC.{u, u, w} (α := α) (β := β) h k)

/-- **The claim in the proof of (18.3)**, page 287, for a connected surface
that is not a sphere, disc or cylinder. -/
theorem isWellRooted_classCCuffs_of_steps (hcut : CutStepStatement.{u, w})
    (hsplit : SplitStepStatement.{u, w}) {h k : ℕ}
    (hlow : ∀ k', ClassCWellRooted.{u, w} (h - 1) k')
    (hprev : 1 ≤ k → ClassCWellRooted.{u, w} h (k - 1))
    {S : Type w} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hg : surfaceComplexity S ≤ h) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) {α β : Type u} [Infinite α]
    (κ : Set S → ℕ) :
    IsWellRootedGraftClass {X : Graft α β | X ∈ classCCuffs S κ ∧ X.index ≤ k} := by
  classical
  have : T2Space S := hS.2.1
  intro X hX
  by_cases hfirst : ∃ j, 0 < j ∧ IsGraftSimulatedIn (X 0) (X j)
  · obtain ⟨j, hj, hsim⟩ := hfirst
    exact ⟨0, j, hj, hsim⟩
  push Not at hfirst
  choose gd hgd using fun n => (hX n).1
  have hidx : ∀ n, (X n).index ≤ k := fun n => (hX n).2
  -- `g(Σ) ≥ 1`, so the lower classes are `𝒞(h - 1, ·)`
  have hgS : surfaceComplexity S = 4 * a + 2 * b + c := by
    rw [surfaceComplexity_eq_connected]; exact connectedSurfaceComplexity_eq he
  have hcutC : ∀ {α' β' : Type u} [Infinite α'] (Y : Graft α' β')
      (DY : GraftDrawing Y.G Y.T S) (F : Set S) (N : ℕ), GM07.IsSchism F →
      DY.drawing.IsNormal F → F ∩ bd S = ∅ → (DY.drawing.V ∩ F).ncard ≤ N → Y.index ≤ k →
      Y ∈ WGraftClass (isoGraftClass (classC.{u, u, w} (h - 1) (k + 2 * N + 2))) := by
    intro α' β' _ Y DY F N hF hFn hFb hFN hYk
    obtain ⟨h', hh', hY⟩ := hcut S hS a b c h3 he α' β' Y DY F N k hF hFn hFb hFN hYk
    exact WGraftClass_mono (isoGraftClass_mono (classC_mono (by omega) le_rfl)) hY
  by_cases hcuffs : (cuffs S).Nonempty
  · -- surfaces with cuffs: (18.1) for the root-leaf drawings
    have hncyl := GM07.not_cylinder_of_model hS h3 he
    obtain ⟨N, hN⟩ := Proofs.theorem_18_1_leaf hS a b c h3 he hncyl hcuffs (gd 0)
    let 𝒟 : Set (Graft (α ⊕ α) (β ⊕ α)) :=
      WGraftClass (isoGraftClass (classC.{u, u, w} (h - 1) (k + 2 * N + 2))) ∪
        {Z | 1 ≤ k ∧ Z ∈ WGraftClass (graftDirectSumClass
          (isoGraftClass (classC.{u, u, w} h (k - 1)))
          (isoGraftClass (classB (2 * (k : ℤ) - 1))))}
    have hmem : ∀ n, rootLeafGraft (X (n + 1)) ∈ 𝒟 := by
      intro n
      have hk' : (rootLeafGraft (X (n + 1))).index ≤ k := by
        rw [rootLeafGraft_index]; exact hidx _
      rcases hN (X (n + 1)) (gd (n + 1)) with hsim | ⟨C, hC, hne⟩ | ⟨DX', hcount, hout⟩
      · exact absurd hsim (hfirst (n + 1) n.succ_pos)
      · exact absurd ((hgd (n + 1) C hC).trans (hgd 0 C hC).symm) hne
      · rcases hout with ⟨C, hC, F, hFn, hFo, hFs, hFb, hlt⟩ | ⟨F, hF, hFn, hFb, hFN⟩
        · right
          have hCk : (DX'.drawing.V ∩ C).ncard ≤ k := by
            have h1 := GraftDrawing.index_eq DX'
            refine le_trans (ncard_le_ncard (inter_subset_inter_right _
              (GM07.connectedComponentIn_subset_of_cuff hC)) (DX'.drawing.finite_V.subset
                inter_subset_left)) ?_
            omega
          refine ⟨by omega, ?_⟩
          refine WGraftClass_mono (graftDirectSumClass_mono (isoGraftClass_mono
            (classCSurface_subset_classC hS hg)) le_rfl) ?_
          exact hsplit S hS a b c h3 he _ _ (rootLeafGraft (X (n + 1))) DX' C F k hC hFn hFo
            hFs hFb hlt hk'
        · exact Or.inl (hcutC _ DX' F N hF hFn hFb hFN hk')
    have h𝒟 : IsWellRootedGraftClass 𝒟 := by
      refine theorem_4_2_proof (theorem_13_3_proof (isWellRootedGraftClass_isoGraftClass (hlow _ _ _))) ?_
      by_cases hk : 1 ≤ k
      · refine isWellRootedGraftClass_mono (fun Z hZ => hZ.2) ?_
        refine theorem_13_3_proof (theorem_13_1_proof (isWellRootedGraftClass_isoGraftClass
          (hprev hk _ _)) (isWellRootedGraftClass_isoGraftClass ?_))
        have : (2 * (k : ℤ) - 1) = ((2 * k - 1 : ℕ) : ℤ) := by omega
        rw [this]
        exact theorem_17_3_proof _
      · intro Z hZ
        exact absurd (hZ 0).1 hk
    obtain ⟨i, j, hij, hsim⟩ := h𝒟 (fun n => rootLeafGraft (X (n + 1))) hmem
    exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, isGraftSimulatedIn_of_rootLeafGraft hsim⟩
  · -- closed surfaces: the printed (18.1)
    have hbd : bd S = ∅ := by
      rw [← sUnion_cuffs, not_nonempty_iff_eq_empty.mp hcuffs, sUnion_empty]
    have hclosed : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x => by
      by_contra hx
      have hx' : x ∈ bd S := hx
      rw [hbd] at hx'
      exact hx'⟩
    have hc0 : c = 0 := by
      have := GM07.ncard_cuffs_of_homeomorph_surfaceModel he
      rw [not_nonempty_iff_eq_empty.mp hcuffs, ncard_empty] at this
      omega
    subst hc0
    have hns : ¬ IsSphere S := GM07.not_isSphere_of_model he (by omega)
    obtain ⟨N, hN⟩ := Proofs.theorem_18_1_closed hclosed hns a b (by omega) he (X 0) (gd 0)
    have hmem : ∀ n, X (n + 1) ∈
        WGraftClass (isoGraftClass (classC.{u, u, w} (α := α) (β := β) (h - 1)
          (k + 2 * N + 2))) := by
      intro n
      rcases hN (X (n + 1)) (gd (n + 1)) with hsim | ⟨F, hF, hFn, hFN⟩
      · exact absurd hsim (hfirst (n + 1) n.succ_pos)
      · refine hcutC _ (gd (n + 1)) F N hF hFn ?_ hFN (hidx _)
        rw [hbd, inter_empty]
    obtain ⟨i, j, hij, hsim⟩ := theorem_13_3_proof (isWellRootedGraftClass_isoGraftClass
      (hlow _ _ _)) (fun n => X (n + 1)) hmem
    exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, hsim⟩

end GraphMinor.GM08
