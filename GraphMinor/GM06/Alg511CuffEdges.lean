module

public import GraphMinor.GM06.Alg511ArcEdge
import GraphMinor.GM07.Section9MoveOff
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section4
import Mathlib.Tactic

/-!
# Exact edges on both cuffs of the input drawing

For the drawing data of VI (5.11), page 134, the auxiliary cuff
edges must use the same fixed labels on both cuffs. Exchange the
radii while retaining the angle, carry the drawing through this
homeomorphism, and apply the exact inner-gap theorem. Transporting
the edge back gives the exact outer gap, including the one-vertex
loop. No linkage or feasible target is used in this construction.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Exchange the inner and outer radii of the concrete cylinder.
This identifies the two cuff input constructions. -/
@[expose] noncomputable def alg511CuffSwap : ClosedCylinder ≃ₜ ClosedCylinder where
  toFun p := ⟨(3 - p.val.1, p.val.2), by
    refine ⟨⟨?_, ?_⟩, trivial⟩ <;> linarith [p.property.1.1, p.property.1.2]⟩
  invFun p := ⟨(3 - p.val.1, p.val.2), by
    refine ⟨⟨?_, ?_⟩, trivial⟩ <;> linarith [p.property.1.1, p.property.1.2]⟩
  left_inv p := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv p := by apply Subtype.ext; apply Prod.ext <;> simp
  continuous_toFun := Continuous.subtype_mk
    ((continuous_const.sub (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)) (fun p => by
        refine ⟨⟨?_, ?_⟩, trivial⟩ <;>
          dsimp only [Pi.sub_apply, Function.comp_apply, Prod.fst] <;>
          linarith [p.property.1.1, p.property.1.2])
  continuous_invFun := Continuous.subtype_mk
    ((continuous_const.sub (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)) (fun p => by
        refine ⟨⟨?_, ?_⟩, trivial⟩ <;>
          dsimp only [Pi.sub_apply, Function.comp_apply, Prod.fst] <;>
          linarith [p.property.1.1, p.property.1.2])

private theorem cuffSwap_twice (p : ClosedCylinder) : alg511CuffSwap (alg511CuffSwap p) = p :=
  by apply Subtype.ext; apply Prod.ext <;> simp [alg511CuffSwap]

private theorem cuffSwap_image_image (A : Set ClosedCylinder) :
    alg511CuffSwap '' (alg511CuffSwap '' A) = A := by
  rw [image_image]
  have hf : (fun p => alg511CuffSwap (alg511CuffSwap p)) = id := funext cuffSwap_twice
  rw [hf, image_id]

/-- Exchanging the radii carries each prescribed inner point to
its prescribed outer point with the same angular index. -/
theorem alg511CuffSwap_M1 {k : ℕ} (i : Fin k) :
    alg511CuffSwap (cylinderM1Point k i) = cylinderM2Point k i := by
  apply Subtype.ext
  apply Prod.ext
  · norm_num [alg511CuffSwap, cylinderM1Point, cylinderM2Point, cylinderPoint]
  · rfl

/-- Exchanging the radii carries each prescribed outer point to
its prescribed inner point with the same angular index. -/
theorem alg511CuffSwap_M2 {k : ℕ} (i : Fin k) :
    alg511CuffSwap (cylinderM2Point k i) = cylinderM1Point k i := by
  rw [← alg511CuffSwap_M1 i, cuffSwap_twice]

private theorem cuffSwap_boundary_iff (p : ClosedCylinder) :
    alg511CuffSwap p ∈ bd ClosedCylinder ↔ p ∈ bd ClosedCylinder := by
  rw [bd_closedCylinder]
  change (3 - p.val.1 = 1 ∨ 3 - p.val.1 = 2) ↔ (p.val.1 = 1 ∨ p.val.1 = 2)
  constructor <;> rintro (h | h)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

private theorem cuffSwap_boundary : alg511CuffSwap '' bd ClosedCylinder = bd ClosedCylinder := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (cuffSwap_boundary_iff q).mpr hq
  · intro hp
    exact ⟨alg511CuffSwap p, (cuffSwap_boundary_iff p).mpr hp, cuffSwap_twice p⟩

private theorem cuffSwap_M1_image (k : ℕ) : alg511CuffSwap '' cylinderM1 k = cylinderM2 k := by
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (alg511CuffSwap_M1 i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨cylinderM1Point k i, ⟨i, rfl⟩, alg511CuffSwap_M1 i⟩

private theorem cuffSwap_M2_image (k : ℕ) : alg511CuffSwap '' cylinderM2 k = cylinderM1 k := by
  rw [← cuffSwap_M1_image k, cuffSwap_image_image]

/-- Carry an input drawing through the radius-exchange homeomorphism. -/
noncomputable def alg511CuffSwapDrawing (G : Drawing ClosedCylinder) : Drawing ClosedCylinder :=
  GM07.embedDrawing alg511CuffSwap.isClosedEmbedding G

/-- The exchanged drawing has precisely the exchanged point set. -/
theorem alg511CuffSwapDrawing_U (G : Drawing ClosedCylinder) :
    (alg511CuffSwapDrawing G).U = alg511CuffSwap '' G.U := GM07.embedDrawing_U _ _

/-- The exchanged drawing has precisely the exchanged vertices. -/
theorem alg511CuffSwapDrawing_V (G : Drawing ClosedCylinder) :
    (alg511CuffSwapDrawing G).V = alg511CuffSwap '' G.V := GM07.embedDrawing_V _ _

/-- The exchanged drawing has precisely the exchanged edges. -/
theorem alg511CuffSwapDrawing_E (G : Drawing ClosedCylinder) :
    (alg511CuffSwapDrawing G).E = (image alg511CuffSwap) '' G.E := by
  let : Nonempty ClosedCylinder := ⟨cylinderPoint 1 (by simp) 0⟩
  exact GM07.embedDrawing_E _ _

private theorem cuffSwap_subdrawing {G F : Drawing ClosedCylinder} (hGF : G.IsSubdrawing F) :
    (alg511CuffSwapDrawing G).IsSubdrawing (alg511CuffSwapDrawing F) := by
  constructor
  · rw [alg511CuffSwapDrawing_V, alg511CuffSwapDrawing_V]
    exact image_mono hGF.1
  · rw [alg511CuffSwapDrawing_E, alg511CuffSwapDrawing_E]
    exact image_mono hGF.2

private theorem cuffSwap_section5 {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) : IsCylinderSection5Drawing k (alg511CuffSwapDrawing G) := by
  refine ⟨hG.1, ?_, ?_⟩
  · intro p hp
    have hpU : p ∈ alg511CuffSwap '' G.U := by
      rw [← alg511CuffSwapDrawing_U]
      exact hp.2
    obtain ⟨q, hq, hqp⟩ := hpU
    have hqbd : q ∈ bd ClosedCylinder := (cuffSwap_boundary_iff q).mp (hqp.symm ▸ hp.1)
    rw [alg511CuffSwapDrawing_V]
    exact ⟨q, hG.2.1 ⟨hqbd, hq⟩, hqp⟩
  · rw [alg511CuffSwapDrawing_V]
    calc
      (alg511CuffSwap '' G.V) ∩ bd ClosedCylinder =
          alg511CuffSwap '' (G.V ∩ bd ClosedCylinder) := by
        rw [image_inter alg511CuffSwap.injective, cuffSwap_boundary]
      _ = alg511CuffSwap '' (cylinderM1 k ∪ cylinderM2 k) := congrArg (image alg511CuffSwap) hG.2.2
      _ = cylinderM1 k ∪ cylinderM2 k := by
        rw [image_union, cuffSwap_M1_image, cuffSwap_M2_image, union_comm]

/-- The prescribed outer-cuff gap with the same increasing angular
parameter as the prescribed inner-cuff gap. -/
@[expose] noncomputable def alg511OuterCuffGapCurve (k : ℕ) (i : Fin k) : Curve ClosedCylinder :=
  ⟨fun t => alg511CuffSwap (initialCuffGapCurve k i t),
    alg511CuffSwap.continuous.comp (initialCuffGapCurve k i).continuous⟩

/-- Every prescribed outer gap is an entire edge in the cuff-augmented
drawing, including the full outer loop when there is one cuff vertex. -/
theorem alg511_exists_exact_outer_gap_edge
    {k : ℕ} {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) (i : Fin k) :
    ∃ e ∈ F.E, e = alg511OuterCuffGapCurve k i '' Set.Ioo 0 1 := by
  have hswapU : (alg511CuffSwapDrawing F).U =
      (alg511CuffSwapDrawing G).U ∪ bd ClosedCylinder := by
    rw [alg511CuffSwapDrawing_U, hFU, image_union,
      alg511CuffSwapDrawing_U, cuffSwap_boundary]
  have hswapV : (alg511CuffSwapDrawing F).V = (alg511CuffSwapDrawing G).V := by
    rw [alg511CuffSwapDrawing_V, alg511CuffSwapDrawing_V, hFV]
  obtain ⟨e', he', hgap⟩ := alg511_exists_exact_initial_gap_edge (cuffSwap_section5 hG)
    (cuffSwap_subdrawing hGF) hswapU hswapV i
  rw [alg511CuffSwapDrawing_E] at he'
  obtain ⟨e, he, heq⟩ := he'
  refine ⟨e, he, ?_⟩
  calc
    e = alg511CuffSwap '' e' := by rw [← heq, cuffSwap_image_image]
    _ = alg511CuffSwap '' (initialCuffGapCurve k i '' Set.Ioo 0 1) := congrArg (image alg511CuffSwap) hgap
    _ = alg511OuterCuffGapCurve k i '' Set.Ioo 0 1 := by rw [image_image]; rfl

end GraphMinor.GM06
