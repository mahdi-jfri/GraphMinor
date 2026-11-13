module

public import GraphMinor.GM08.Section18LeafDrawing
public import GraphMinor.GM08.Section18Reduction
import GraphMinor.GM07.Section8
import GraphMinor.GM08.Section17LeafReflect
import GraphMinor.GM08.Section18LeafSchism
import GraphMinor.GM08.Section18Minimum

/-!
# VIII (18.1) for the root-leaf drawings

The paper derives (18.1) from VII (9.1) and the remark on page 242 of VII
that every schismatic set includes a schism. That remark is false (see the
correction on page 242 in `corrections/GM07.md`), and the printed (18.1)
fails on a surface with three cuffs (see the correction to (18.1) in
`corrections/GM08.md`). Here we
prove the form of (18.1) that the proof of (18.3) needs.

Draw every graft with its roots made into leaves (`exists_leaf_graftDrawing`).
In such a drawing every vertex on the boundary has one edge, a spoke of a
collar. Collapsing the spokes moves every alpha candidate off the boundary
without adding vertices, so a small alpha gives a small schism
(`exists_normal_schism_of_retraction`). The root-leaf grafts have the same
cuff counts as the old ones, and a simulation of the root-leaf grafts gives a
simulation of the old ones (`isGraftSimulatedIn_of_rootLeafGraft`). So the
alternatives of (18.1) hold, with (iii) and (iv) for the root-leaf drawing.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11

universe u v w

variable {S : Type w} [TopologicalSpace S]

section LeafDrawing

variable {K : BoundaryCollar S (bd S)} {Γ H : Drawing S}

/-- A point whose push lies in the leaf drawing lies in the old drawing. -/
theorem BoundaryCollar.mem_U_of_e_mem (hU : H.U = K.e '' Γ.U ∪ ⋃ x ∈ Γ.V ∩ bd S, K.sp x)
    {z : S} (hz : K.e z ∈ H.U) : z ∈ Γ.U := by
  rw [hU] at hz
  rcases hz with ⟨y, hy, hyz⟩ | hz
  · exact K.inj_e hyz ▸ hy
  · obtain ⟨x, hx, hzs⟩ := mem_iUnion₂.mp hz
    have h : K.e z ∈ K.sp x ∩ range K.e := ⟨hzs, z, rfl⟩
    rw [K.sp_range x hx.2] at h
    rw [K.inj_e h]
    exact Γ.V_subset_U hx.1

/-- The collapse sends a point into the leaf drawing only if the point is
already in it. -/
theorem BoundaryCollar.leaf_hU (hΓ : Γ.IsProper)
    (hU : H.U = K.e '' Γ.U ∪ ⋃ x ∈ Γ.V ∩ bd S, K.sp x) (y : S) (hy : K.g y ∈ H.U) :
    y ∈ H.U := by
  rcases K.cover y with ⟨z, rfl⟩ | ⟨x₀, hx₀, hys, hg⟩
  · rw [K.g_e] at hy
    rw [hU]
    exact .inl ⟨z, K.mem_U_of_e_mem hU hy, rfl⟩
  · rw [hg] at hy
    have hx₀U := K.mem_U_of_e_mem hU hy
    have hx₀V : x₀ ∈ Γ.V := hΓ ⟨hx₀, hx₀U⟩
    rw [hU]
    exact .inr (mem_iUnion₂.mpr ⟨x₀, ⟨hx₀V, hx₀⟩, hys⟩)

/-- The collapse sends the vertices of the leaf drawing to vertices. -/
theorem BoundaryCollar.leaf_hV (hV : H.V = K.e '' Γ.V ∪ (Γ.V ∩ bd S)) (y : S)
    (hy : y ∈ H.V) : K.g y ∈ H.V := by
  rw [hV] at hy ⊢
  rcases hy with ⟨v, hv, rfl⟩ | hy
  · rw [K.g_e]; exact .inl ⟨v, hv, rfl⟩
  · rw [K.g_of_mem_bd hy.2]; exact .inl ⟨y, hy.1, rfl⟩

/-- The leaf drawing has the same vertices on each cuff. -/
theorem BoundaryCollar.leaf_cuff_count (hS : IsSurface S)
    (hV : H.V = K.e '' Γ.V ∪ (Γ.V ∩ bd S)) {C : Set S} (hC : C ∈ cuffs S) :
    H.V ∩ C = Γ.V ∩ C := by
  have : T2Space S := hS.2.1
  have hCb : C ⊆ bd S := connectedComponentIn_subset_of_cuff hC
  rw [hV]
  ext z
  constructor
  · rintro ⟨⟨v, -, rfl⟩ | hz, hzC⟩
    · exact absurd (hCb hzC) (K.e_not_mem_bd v)
    · exact ⟨hz.1, hzC⟩
  · rintro ⟨hz, hzC⟩
    exact ⟨.inr ⟨hz, hCb hzC⟩, hzC⟩

end LeafDrawing

/-- **VIII (18.1) for root-leaf drawings.** Let `S` have a cuff and not be a
sphere, disc or cylinder, and let `Y` be drawn in `S`. Then there is `N` such
that for every graft `X` drawn in `S`, either `Y` is simulated in `X`, or the
cuff counts differ, or the root-leaf graft of `X` has a drawing in `S` with the
same cuff counts as `X` in which (18.1)(iv) holds, or there is a normal schism
with at most `N` vertices that misses the boundary. -/
theorem Proofs.theorem_18_1_leaf [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c) (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (hcuffs : (cuffs S).Nonempty)
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      ∃ DX' : GraftDrawing (rootLeafGraft X).G (rootLeafGraft X).T S,
        (∀ C ∈ cuffs S, DX'.drawing.V ∩ C = DX.drawing.V ∩ C) ∧
        ((∃ C ∈ cuffs S, ∃ F : Set S, DX'.drawing.IsNormal F ∧ IsOArc F ∧
            GM07.SurroundsCuff F C ∧ F ∩ bd S ⊆ C ∧
            (DX'.drawing.V ∩ F).ncard < (DX'.drawing.V ∩ C).ncard) ∨
          ∃ F : Set S, GM07.IsSchism F ∧ DX'.drawing.IsNormal F ∧ F ∩ bd S = ∅ ∧
            (DX'.drawing.V ∩ F).ncard ≤ N) := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hns : ¬ IsSphere S := GM07.not_isSphere_of_model he (by omega)
  obtain ⟨K⟩ := exists_boundaryCollar hS
  obtain ⟨DY', -, hDY'V⟩ := K.exists_leaf_graftDrawing DY
  obtain ⟨N, hN⟩ := exists_simulation_or_cuff_count_or_surrounding_or_small_alpha hS a b c h3
    he hncyl DY'
  refine ⟨N, fun X DX => ?_⟩
  obtain ⟨DX', hDX'U, hDX'V⟩ := K.exists_leaf_graftDrawing DX
  have hcount : ∀ C ∈ cuffs S, DX'.drawing.V ∩ C = DX.drawing.V ∩ C :=
    fun C hC => K.leaf_cuff_count hS hDX'V hC
  rcases hN (rootLeafGraft X) DX' with hsim | ⟨C, hC, hne⟩ | hiv | hα
  · exact .inl (isGraftSimulatedIn_of_rootLeafGraft hsim)
  · refine .inr (.inl ⟨C, hC, ?_⟩)
    rwa [hcount C hC, K.leaf_cuff_count hS hDY'V hC] at hne
  · exact .inr (.inr ⟨DX', hcount, .inl hiv⟩)
  · refine .inr (.inr ⟨DX', hcount, .inr ?_⟩)
    obtain ⟨X₀, hsch, hnorm, hcard⟩ :=
      exists_normal_schismatic_at_alpha hS h3 he hncyl DX'.drawing DX'.isProper
    have hsc := GM07.IsSchismatic.isSolid_and_isConnected hS hsch
    have hcand : GM07.IsAlphaCandidate DX'.drawing X₀ := ⟨hsc.1, hsc.2, hnorm, hsch.2.1⟩
    obtain ⟨F, hF, hFn, hFbd, hFc⟩ := exists_normal_schism_of_retraction hS h3 he hns hcuffs
      DX'.drawing K.cont_Φ K.Φ_zero K.Φ_one K.g_not_mem_bd
      (K.leaf_hU DX.isProper hDX'U) (fun y hy _ => K.leaf_hV hDX'V y hy) hcand
    refine ⟨F, hF, hFn, hFbd, hFc.trans ?_⟩
    rw [inter_comm] at hcard
    omega

end GraphMinor.GM08
