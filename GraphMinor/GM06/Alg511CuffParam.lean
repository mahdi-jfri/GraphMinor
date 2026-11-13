module

public import GraphMinor.GM06.Alg511CuffEnumeration
public import GraphMinor.GM11.Rotation
public import GraphMinor.GM06.Section5CapDrawing
import Mathlib.Tactic

/-!
# Parametrizations with fixed cuff directions

For the drawing input of VI (5.11), page 134, the successor program's
cuff markers must refer to prescribed parameter ends. Each gap curve
is injective on its open parameter interval, even when there is one
cuff vertex and its two ends coincide. Use these curves for the added
edges and retain the supplied parametrizations on all original edges.
The resulting interpretation fixes both directions of every marker.
All choices occur in an existence proof, outside the finite input.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The prescribed angular gap does not repeat an interior point,
including the full gap of a one-vertex cuff. -/
theorem alg511_initial_gap_injOn {k : ℕ} (hk : 0 < k) (i : Fin k) :
    InjOn (initialCuffGapCurve k i) (Ioo 0 1) := by
  intro s hs t ht hst
  have he : Circle.exp (2 * (((i.val + 1 : ℕ) : ℝ) + (s : ℝ)) * π / k) =
      Circle.exp (2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k) :=
    congrArg (fun p : ClosedCylinder => p.val.2) hst
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hscale := congrArg (fun a : ℝ => a * ((k : ℝ) / (2 * π))) hm
  have hleft : (2 * (((i.val + 1 : ℕ) : ℝ) + (s : ℝ)) * π / k) *
      ((k : ℝ) / (2 * π)) = ((i.val + 1 : ℕ) : ℝ) + (s : ℝ) := by
    field_simp [hkne, pi_ne_zero]
  have hright : (2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k +
      (m : ℝ) * (2 * π)) * ((k : ℝ) / (2 * π)) =
      ((i.val + 1 : ℕ) : ℝ) + (t : ℝ) + (m : ℝ) * k := by
    field_simp [hkne, pi_ne_zero]
  rw [hleft, hright] at hscale
  have hlo : (-1 : ℝ) < (m : ℝ) * k := by
    have hs0 : (0 : ℝ) < s := hs.1
    have ht1 : (t : ℝ) < 1 := ht.2
    linarith
  have hhi : (m : ℝ) * k < 1 := by
    have hs1 : (s : ℝ) < 1 := hs.2
    have ht0 : (0 : ℝ) < t := ht.1
    linarith
  have hloZ : (-1 : ℤ) < m * (k : ℤ) := by exact_mod_cast hlo
  have hhiZ : m * (k : ℤ) < (1 : ℤ) := by exact_mod_cast hhi
  have hmzero : m * (k : ℤ) = 0 := by omega
  have hmR : (m : ℝ) * k = 0 := by exact_mod_cast hmzero
  apply Subtype.ext
  linarith

/-- Exchanging the radii retains injectivity of each outer gap on
its open parameter interval. -/
theorem alg511_outer_gap_injOn {k : ℕ} (hk : 0 < k) (i : Fin k) :
    InjOn (alg511OuterCuffGapCurve k i) (Ioo 0 1) := by
  intro s hs t ht hst
  exact alg511_initial_gap_injOn hk i hs ht (alg511CuffSwap.injective hst)

/-- The outer gap runs from its indexed outer vertex to the next
one, with the same parameter direction as the inner gap. -/
theorem alg511_outer_gap_ends {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    alg511OuterCuffGapCurve k i 0 = cylinderM2Point k i ∧
      alg511OuterCuffGapCurve k i 1 = cylinderM2Point k (finSuccCycle i) := by
  have h := initialCuffGapCurve_props hG i
  constructor
  · change alg511CuffSwap (initialCuffGapCurve k i 0) = _
    rw [h.1, alg511CuffSwap_M1]
  · change alg511CuffSwap (initialCuffGapCurve k i 1) = _
    rw [h.2.1, alg511CuffSwap_M1]

/-- Adjoining the cuffs allows edge parametrizations that preserve
all original edge curves and use exactly the prescribed increasing
angular curve on each new inner and outer edge. -/
theorem alg511_exists_cuff_edgePar {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    {γ₀ : Set ClosedCylinder → I → ClosedCylinder} (hγ₀ : EdgePar G γ₀) :
    ∃ γ : Set ClosedCylinder → I → ClosedCylinder, EdgePar F γ ∧
      (∀ e ∈ G.E, γ e = γ₀ e) ∧
      (∀ i : Fin k, γ (initialCuffGapCurve k i '' Ioo 0 1) = initialCuffGapCurve k i) ∧
      (∀ i : Fin k, γ (alg511OuterCuffGapCurve k i '' Ioo 0 1) = alg511OuterCuffGapCurve k i) := by
  classical
  obtain ⟨e, heG, heI, heO⟩ := alg511_exists_cuff_edge_equiv hG hGF hFU hFV
  let f : G.E ⊕ (Fin k ⊕ Fin k) → I → ClosedCylinder := fun a => match a with
    | .inl a => γ₀ a.val
    | .inr (.inl i) => initialCuffGapCurve k i
    | .inr (.inr i) => alg511OuterCuffGapCurve k i
  let γ : Set ClosedCylinder → I → ClosedCylinder := fun a =>
    if ha : a ∈ F.E then f (e.symm ⟨a, ha⟩) else γ₀ a
  have hγ (a : G.E ⊕ (Fin k ⊕ Fin k)) : γ (e a).val = f a := by
    dsimp only [γ]
    rw [dite_eq_left (e a).property]
    change f (e.symm (e a)) = f a
    rw [e.symm_apply_apply]
  have hM1 (i : Fin k) : cylinderM1Point k i ∈ F.V := by
    rw [hFV]
    exact (show cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder from
      hG.2.2.symm ▸ Or.inl ⟨i, rfl⟩).1
  have hM2 (i : Fin k) : cylinderM2Point k i ∈ F.V := by
    rw [hFV]
    exact (show cylinderM2Point k i ∈ G.V ∩ bd ClosedCylinder from
      hG.2.2.symm ▸ Or.inr ⟨i, rfl⟩).1
  have hcont (a : G.E ⊕ (Fin k ⊕ Fin k)) : Continuous (f a) := by
    rcases a with a | (i | i)
    · exact hγ₀.cont a.val a.property
    · exact (initialCuffGapCurve k i).continuous
    · exact (alg511OuterCuffGapCurve k i).continuous
  have hzero (a : G.E ⊕ (Fin k ⊕ Fin k)) : f a 0 ∈ F.V := by
    rcases a with a | (i | i)
    · rw [hFV]
      exact hγ₀.zero a.val a.property
    · change initialCuffGapCurve k i 0 ∈ F.V
      rw [(initialCuffGapCurve_props hG i).1]
      exact hM1 i
    · change alg511OuterCuffGapCurve k i 0 ∈ F.V
      rw [(alg511_outer_gap_ends hG i).1]
      exact hM2 i
  have hone (a : G.E ⊕ (Fin k ⊕ Fin k)) : f a 1 ∈ F.V := by
    rcases a with a | (i | i)
    · rw [hFV]
      exact hγ₀.one a.val a.property
    · change initialCuffGapCurve k i 1 ∈ F.V
      rw [(initialCuffGapCurve_props hG i).2.1]
      exact hM1 (finSuccCycle i)
    · change alg511OuterCuffGapCurve k i 1 ∈ F.V
      rw [(alg511_outer_gap_ends hG i).2]
      exact hM2 (finSuccCycle i)
  have hinj (a : G.E ⊕ (Fin k ⊕ Fin k)) : InjOn (f a) (Ioo 0 1) := by
    rcases a with a | (i | i)
    · exact hγ₀.inj a.val a.property
    · exact alg511_initial_gap_injOn hG.1 i
    · exact alg511_outer_gap_injOn hG.1 i
  have himage (a : G.E ⊕ (Fin k ⊕ Fin k)) : f a '' Ioo 0 1 = (e a).val := by
    rcases a with a | (i | i)
    · exact (hγ₀.image a.val a.property).trans (heG a).symm
    · exact (heI i).symm
    · exact (heO i).symm
  have hpar : EdgePar F γ := {
    cont := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hγ]
      exact hcont b
    zero := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hγ]
      exact hzero b
    one := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hγ]
      exact hone b
    inj := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hγ]
      exact hinj b
    image := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hγ]
      exact himage b }
  refine ⟨γ, hpar, ?_, ?_, ?_⟩
  · intro a ha
    have h := hγ (.inl ⟨a, ha⟩)
    rw [heG] at h
    exact h
  · intro i
    have h := hγ (.inr (.inl i))
    rw [heI] at h
    exact h
  · intro i
    have h := hγ (.inr (.inr i))
    rw [heO] at h
    exact h

/-- Carry every chosen edge curve into the sphere while retaining
its parameter direction. The sphere's polar rotations therefore
refer to the same fixed inner and outer cuff ends. -/
theorem alg511_exists_sphere_edgePar {F : Drawing ClosedCylinder}
    {γ : Set ClosedCylinder → I → ClosedCylinder} (hγ : EdgePar F γ) :
    ∃ δ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane,
      EdgePar (cylinderSphereDrawing F) δ ∧
      ∀ e ∈ F.E, ∀ t : I, δ (cylinderToSphere '' e) t = cylinderToSphere (γ e t) := by
  classical
  let e : F.E ≃ (cylinderSphereDrawing F).E :=
    (Equiv.Set.image (fun a : Set ClosedCylinder => cylinderToSphere '' a) F.E
      (Set.image_injective.mpr injective_cylinderToSphere)).trans
        (Set.equivOfEq (cylinderSphereDrawing_E F).symm)
  let δ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane := fun a t =>
    if ha : a ∈ (cylinderSphereDrawing F).E then
      cylinderToSphere (γ (e.symm ⟨a, ha⟩).val t)
    else cylinderToSphere (cylinderPoint 1 (by simp) 0)
  have he (a : F.E) : (e a).val = cylinderToSphere '' a.val := rfl
  have hδ (a : F.E) : δ (e a).val = fun t => cylinderToSphere (γ a.val t) := by
    funext t
    dsimp only [δ]
    rw [dite_eq_left (e a).property]
    change cylinderToSphere (γ (e.symm (e a)).val t) = _
    rw [e.symm_apply_apply]
  have hδpar : EdgePar (cylinderSphereDrawing F) δ := {
    cont := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hδ]
      exact continuous_cylinderToSphere.comp (hγ.cont b.val b.property)
    zero := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hδ, cylinderSphereDrawing_V]
      exact mem_image_of_mem _ (hγ.zero b.val b.property)
    one := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hδ, cylinderSphereDrawing_V]
      exact mem_image_of_mem _ (hγ.one b.val b.property)
    inj := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hδ]
      intro s hs t ht hst
      exact hγ.inj b.val b.property hs ht (injective_cylinderToSphere hst)
    image := by
      intro a ha
      obtain ⟨b, hb⟩ := e.surjective ⟨a, ha⟩
      have hval : (e b).val = a := congrArg Subtype.val hb
      rw [← hval, hδ, ← image_image, hγ.image b.val b.property, he] }
  refine ⟨δ, hδpar, ?_⟩
  intro a ha t
  have h := congrFun (hδ ⟨a, ha⟩) t
  rw [he] at h
  exact h

end GraphMinor.GM06
