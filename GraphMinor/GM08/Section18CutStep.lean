module

public import GraphMinor.GM08.Section18Step
public import GraphMinor.GM08.Section18CutGraft
import GraphMinor.GM08.Section18Theorem182
import GraphMinor.GM08.Section18CircleCut
import GraphMinor.GM08.Section18SchismBoundary

/-!
# The cut step of (18.3)

This is case (i) on page 287 of VIII. The graft has a drawing with a normal
schism `F` that misses the boundary and has at most `N` vertices. Since `F`
misses the boundary, it has type (i), (iv) or (v). We cut along `F`, so that
the measure `g` drops by (18.2), and use `mem_WGraftClass_classC_of_cut`. Each
point of `F` has two lifts, except for the branch points of an `X₁`-, `X₂`- or
`X₃`-arc, which add two more lifts in all. So the vertices on `F` have at most
`2N + 2` lifts.

Type (i) is proved here (`cutStep_oArc`). For types (iv) and (v) we need a
cut with these lift counts and with a smaller measure; this is
`CutCountStatement`, and `cutStepStatement_of_cutCount` derives
`CutStepStatement` from it.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u w

/-- If every fibre over a finite set `A` has at most `c` points, the preimage
of `A` has at most `c |A|` points. -/
theorem ncard_preimage_le_mul {X Y : Type*} (ψ : Y → X) {A : Set X} (hA : A.Finite) {c : ℕ}
    (h : ∀ x ∈ A, (ψ ⁻¹' {x}).ncard ≤ c) : (ψ ⁻¹' A).ncard ≤ c * A.ncard := by
  induction A, hA using Set.Finite.induction_on with
  | empty => simp
  | @insert a s ha hs ih =>
    rw [ncard_insert_of_notMem ha hs, insert_eq, preimage_union]
    calc (ψ ⁻¹' {a} ∪ ψ ⁻¹' s).ncard ≤ (ψ ⁻¹' {a}).ncard + (ψ ⁻¹' s).ncard := ncard_union_le _ _
      _ ≤ c + c * s.ncard :=
        Nat.add_le_add (h a (mem_insert _ _)) (ih fun x hx => h x (mem_insert_of_mem _ hx))
      _ = c * (s.ncard + 1) := by ring

/-- `𝒞(h, k)` grows with `k`. -/
theorem classC_mono_right {α : Type u} {β : Type u} {h k k' : ℕ} (hk : k ≤ k') :
    classC.{u, u, w} (α := α) (β := β) h k ⊆ classC.{u, u, w} h k' := by
  rintro X ⟨S, tS, hS, hg, hX, hE⟩
  exact ⟨S, tS, hS, hg, hX.trans hk, hE⟩

/-- **The cut step for a circle**, type (i) of a schism that misses the
boundary. -/
theorem cutStep_oArc {S : Type w} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {F : Set S} (hF : GM07.IsSchism F) (hO : IsOArc F) (hnp : ¬ GM07.IsNearPlanar F)
    (hoff : F ∩ bd S = ∅) {α β : Type u} [Infinite α] (X : Graft α β)
    (DX : GraftDrawing X.G X.T S) {N k : ℕ} (hn : DX.drawing.IsNormal F)
    (hN : (DX.drawing.V ∩ F).ncard ≤ N) (hk : X.index ≤ k) :
    ∃ h' < surfaceComplexity S,
      X ∈ WGraftClass (isoGraftClass (classC.{u, u, w} h' (k + 2 * N + 2))) := by
  obtain ⟨T, tT, ψ, hT, hcut, hlt⟩ :=
    exists_cut_complexity_lt_of_non_nearPlanar_oArc hS hO (disjoint_iff_inter_eq_empty.mpr hoff) hnp
  have hcutA := isCutAlongSet_of_isCutting hS hT (isClosed_of_isSchism hS hF) hcut
  have hfin : (DX.drawing.V ∩ F).Finite := DX.drawing.finite_V.subset inter_subset_left
  have hM : (ψ ⁻¹' (DX.drawing.V ∩ F)).ncard ≤ 2 * N + 2 := by
    refine (ncard_preimage_le_mul ψ hfin (c := 2) fun x hx => (hcut.2.2.2.1 x hx.2).le).trans ?_
    omega
  refine ⟨surfaceComplexity T, hlt, ?_⟩
  have h := mem_WGraftClass_classC_of_cut hS hF hcutA (GM19.IsCutting.isCutMap hcut) hoff X DX hn
    (fun x hx => by rw [hcut.2.2.2.1 x hx.2]; norm_num) hk hM
  rwa [← Nat.add_assoc] at h

/-- **(18.2) with lift counts** for schisms of types (iv) and (v): there is a
cut along `F` with a smaller measure, in which every point of `F` has at
least two lifts, and any finite subset `A` of `F` has at most `2 |A| + 2`
lifts. -/
def CutCountStatement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (a b c : ℕ), 3 ≤ 3 * a + 3 * b + c → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ F : Set S, GM07.IsSchism F → F ∩ bd S = ∅ →
      (GM07.IsX1Arc F ∨ GM07.IsX2Arc F ∨ GM07.IsX3Arc F) →
      ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
        GM07.IsCutAlongSet F ψ ∧ GM19.IsCutMap ψ F ∧
        surfaceComplexity T < surfaceComplexity S ∧
        (∀ x ∈ F, 1 < (ψ ⁻¹' {x}).ncard) ∧
        ∀ A ⊆ F, A.Finite → (ψ ⁻¹' A).ncard ≤ 2 * A.ncard + 2

/-- The cut step of (18.3) follows from (18.2) with lift counts. -/
theorem cutStepStatement_of_cutCount (hcount : CutCountStatement.{w}) :
    CutStepStatement.{u, w} := by
  intro S _ _ hS a b c habc hmodel α β _ X DX F N k hF hn hoff hN hk
  have hF' := hF
  rcases hF' with ⟨hO, hnp, -⟩ | ⟨⟨u, v, -, hbd, -⟩, -⟩ | ⟨⟨u, v, -, hbd, -⟩, -⟩ | ⟨hX, -⟩ |
      ⟨hX, -⟩ | ⟨w, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbd⟩
  · exact cutStep_oArc hS hF hO hnp hoff X DX hn hN hk
  · exact absurd (hbd.symm.trans hoff) (insert_nonempty _ _).ne_empty
  · exact absurd (hbd.symm.trans hoff) (insert_nonempty _ _).ne_empty
  rotate_right
  · exact absurd (hbd.symm.trans hoff) (singleton_nonempty _).ne_empty
  all_goals
    obtain ⟨T, tT, ψ, hcut, hmap, hlt, hlift, hcnt⟩ :=
      hcount S hS a b c habc hmodel F hF hoff (by tauto)
    have hfin : (DX.drawing.V ∩ F).Finite := DX.drawing.finite_V.subset inter_subset_left
    have hM : (ψ ⁻¹' (DX.drawing.V ∩ F)).ncard ≤ 2 * N + 2 :=
      (hcnt _ inter_subset_right hfin).trans (by omega)
    refine ⟨surfaceComplexity T, hlt, ?_⟩
    have h := mem_WGraftClass_classC_of_cut hS hF hcut hmap hoff X DX hn
      (fun x hx => hlift x hx.2) hk hM
    rwa [← Nat.add_assoc] at h

end GraphMinor.GM08
