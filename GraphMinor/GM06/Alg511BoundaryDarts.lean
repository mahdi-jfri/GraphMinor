module

public import GraphMinor.GM11.Rotation
public import GraphMinor.GM11.Defs
import GraphMinor.GM11.PerimeterCount
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Directed labels for geometrically traced boundary walks

The input rows of VI (5.11), page 134, retain the direction of each
boundary step, including a step along a loop. Restrict an edge curve
to its open parameter interval. Compactness of the closed interval
makes this restriction a homeomorphism onto the open edge. Comparing
two such curves gives a homeomorphism of the open interval, which is
increasing or decreasing. These two cases give the even and odd
labels of the step. Apply this comparison to every step of a traced
walk, retaining its original order and exact edge sequence.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

private theorem open_parameter_homeomorph
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (f : I → S) (hf : Continuous f) {e : Set S}
    (hzero : f 0 ∉ e) (hone : f 1 ∉ e)
    (hinj : InjOn f (Ioo 0 1)) (himage : f '' Ioo 0 1 = e) :
    ∃ h : Ioo (0 : I) 1 ≃ₜ e, ∀ t, (h t).val = f t.val := by
  classical
  have hpre : f ⁻¹' e = Ioo (0 : I) 1 := by
    ext t
    constructor
    · intro ht
      exact ⟨unitInterval.pos_iff_ne_zero.mpr (fun ht0 => hzero (ht0 ▸ ht)),
        unitInterval.lt_one_iff_ne_one.mpr (fun ht1 => hone (ht1 ▸ ht))⟩
    · intro ht
      exact himage ▸ mem_image_of_mem f ht
  let g : (f ⁻¹' e) → e := fun t => ⟨f t.val, t.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro s t hst
      apply Subtype.ext
      exact hinj (hpre ▸ s.property) (hpre ▸ t.property) (congrArg Subtype.val hst)
    · intro p
      obtain ⟨t, ht, htp⟩ := (show p.val ∈ f '' Ioo 0 1 from himage.symm ▸ p.property)
      exact ⟨⟨t, hpre.symm ▸ ht⟩, Subtype.ext htp⟩
  let h : (f ⁻¹' e) ≃ₜ e := (Equiv.ofBijective g hg).toHomeomorphOfContinuousClosed
    (Continuous.subtype_mk (hf.comp continuous_subtype_val) _)
    (hf.isClosedMap.restrictPreimage e)
  exact ⟨(Homeomorph.setCongr hpre.symm).trans h, fun _ => rfl⟩

/-- Two continuous edge parametrizations, injective on their open
intervals, differ there by an increasing or decreasing homeomorphism.
The conclusion also applies when both closed endpoints coincide. -/
theorem alg511_edge_curves_orientation
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (f g : I → S) (hf : Continuous f) (hg : Continuous g) {e : Set S}
    (hfzero : f 0 ∉ e) (hfone : f 1 ∉ e)
    (hgzero : g 0 ∉ e) (hgone : g 1 ∉ e)
    (hfinj : InjOn f (Ioo 0 1)) (hginj : InjOn g (Ioo 0 1))
    (hfimage : f '' Ioo 0 1 = e) (hgimage : g '' Ioo 0 1 = e) :
    ∃ ρ : Ioo (0 : I) 1 ≃ₜ Ioo (0 : I) 1,
      (∀ t, f t.val = g (ρ t).val) ∧ (StrictMono ρ ∨ StrictAnti ρ) := by
  obtain ⟨F, hF⟩ := open_parameter_homeomorph f hf hfzero hfone hfinj hfimage
  obtain ⟨G, hG⟩ := open_parameter_homeomorph g hg hgzero hgone hginj hgimage
  let ρ := F.trans G.symm
  have hρ (t : Ioo (0 : I) 1) : G (ρ t) = F t := G.apply_symm_apply (F t)
  refine ⟨ρ, ?_, ?_⟩
  · intro t
    rw [← hF, ← hG, hρ]
  · classical
    let ψ : I → I := fun t => if ht : t ∈ Ioo 0 1 then (ρ ⟨t, ht⟩).val else 0
    have hψ (t : Ioo (0 : I) 1) : ψ t.val = (ρ t).val := by
      simp only [ψ, dite_eq_left t.property]
    have hψc : ContinuousOn ψ (Ioo 0 1) := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      have heq : (fun t : Ioo (0 : I) 1 => ψ t.val) = fun t => (ρ t).val := funext hψ
      change Continuous (fun t : Ioo (0 : I) 1 => ψ t.val)
      rw [heq]
      exact continuous_subtype_val.comp ρ.continuous
    have hψi : InjOn ψ (Ioo 0 1) := by
      intro s hs t ht hst
      have hst' : (ρ ⟨s, hs⟩).val = (ρ ⟨t, ht⟩).val := by
        rw [← hψ, ← hψ]
        exact hst
      exact congrArg Subtype.val (ρ.injective (Subtype.ext hst'))
    rcases hψc.strictMonoOn_of_injOn_Ioo (show (0 : I) < 1 by norm_num) hψi with hm | ha
    · apply Or.inl
      intro s t hst
      change (ρ s).val < (ρ t).val
      rw [← hψ, ← hψ]
      exact hm s.property t.property hst
    · apply Or.inr
      intro s t hst
      change (ρ t).val < (ρ s).val
      rw [← hψ, ← hψ]
      exact ha s.property t.property hst

private theorem affine_open_image {a b : ℝ} (hab : a < b) :
    (fun t : I => a + (t : ℝ) * (b - a)) '' Ioo 0 1 = Ioo a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : (t : ℝ) < 1 := ht.2
    constructor <;> nlinarith
  · intro hx
    let t : I := ⟨(x - a) / (b - a), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hx.1.le) (sub_nonneg.mpr hab.le)
      · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])⟩
    refine ⟨t, ⟨?_, ?_⟩, ?_⟩
    · change (0 : ℝ) < (x - a) / (b - a)
      exact div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hab)
    · change (x - a) / (b - a) < 1
      exact (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
    · change a + (x - a) / (b - a) * (b - a) = x
      field_simp [sub_ne_zero.mpr hab.ne']
      ring

/-- A row of directed edge labels follows the actual tracing curve
step by step. An even label follows the chosen edge parameter, and
an odd label follows it backwards. The comparison is on the open
edge, so it distinguishes the two directions of a loop. -/
@[expose] def Alg511BoundaryDartsRep
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {m : ℕ}
    (edge : Fin m ≃ G.E) (γ : Set S → I → S) (φ : ℝ → S) :
    (a b : ℝ) → {u v : S} → GraphWalk G.toGraph u v → List ℕ → Prop
  | a, b, u, _, .nil _, [] => a = b ∧ φ a = u
  | a, b, u, _, .cons (e := e) he W, d :: ds =>
      ∃ c : ℝ, a < c ∧ φ a = u ∧ InjOn φ (Ioo a c) ∧ φ '' Ioo a c = e ∧
        ∃ ρ : Ioo (0 : I) 1 ≃ₜ Ioo (0 : I) 1,
          (∀ t, φ (a + (t.val : ℝ) * (c - a)) = γ e (ρ t).val) ∧
          ((d = 2 * (edge.symm ⟨e, he.edge_mem⟩).val ∧ StrictMono ρ) ∨
            (d = 2 * (edge.symm ⟨e, he.edge_mem⟩).val + 1 ∧ StrictAnti ρ)) ∧
          Alg511BoundaryDartsRep edge γ φ c b W ds
  | _, _, _, _, _, _ => False

/-- Every continuously traced boundary walk has directed labels
with its exact order, its exact interpreted edges and valid bounds. -/
theorem alg511_exists_boundary_darts
    {S : Type u} [TopologicalSpace S] [T2Space S] {G : Drawing S} {m : ℕ}
    (edge : Fin m ≃ G.E) {γ : Set S → I → S} (hγ : EdgePar G γ)
    {φ : ℝ → S} (hφ : Continuous φ) {u v : S} (W : GraphWalk G.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn G φ a b W → ∃ ds : List ℕ,
      Alg511BoundaryDartsRep edge γ φ a b W ds ∧
      ds.length = W.edges.length ∧ (∀ d ∈ ds, d < 2 * m) ∧
      ∃ labels : List (Fin m), labels.map Fin.val = ds.map (fun d => d / 2) ∧
        labels.map (fun j => (edge j).val) = W.edges := by
  induction W with
  | nil hu =>
    intro a b hrun
    exact ⟨[], hrun, rfl, by simp, [], rfl, rfl⟩
  | @cons u c v e he W ih =>
    rintro a b ⟨s, has, hstart, hinj, himage, hrest⟩
    obtain ⟨ds, hds, hlen, hbound, labels, hlabels, hedges⟩ := ih hrest
    let f : I → S := fun t => φ (a + (t : ℝ) * (s - a))
    have hf : Continuous f := hφ.comp (by fun_prop)
    have hf0 : f 0 = u := by
      change φ (a + 0 * (s - a)) = u
      simpa only [zero_mul, add_zero] using hstart
    have hf1 : f 1 = c := by
      change φ (a + 1 * (s - a)) = c
      simpa only [one_mul, add_sub_cancel] using (runs_start hrest)
    have hfzero : f 0 ∉ e := fun hp => (he.1.2.1 hp).2 (hf0.symm ▸ he.left_mem)
    have hfone : f 1 ∉ e := fun hp => (he.1.2.1 hp).2 (hf1.symm ▸ he.right_mem)
    have hfinj : InjOn f (Ioo 0 1) := by
      intro t ht q hq htq
      have ht' : a + (t : ℝ) * (s - a) ∈ Ioo a s :=
        affine_open_image has ▸ mem_image_of_mem _ ht
      have hq' : a + (q : ℝ) * (s - a) ∈ Ioo a s :=
        affine_open_image has ▸ mem_image_of_mem _ hq
      have heq := hinj ht' hq' htq
      apply Subtype.ext
      exact mul_right_cancel₀ (sub_ne_zero.mpr has.ne') (add_left_cancel heq)
    have hfimage : f '' Ioo 0 1 = e := by
      change (fun t : I => φ (a + (t : ℝ) * (s - a))) '' Ioo 0 1 = e
      rw [← image_image, affine_open_image has, himage]
    have hgzero : γ e 0 ∉ e := fun hp => (he.1.2.1 hp).2 (hγ.zero e he.edge_mem)
    have hgone : γ e 1 ∉ e := fun hp => (he.1.2.1 hp).2 (hγ.one e he.edge_mem)
    obtain ⟨ρ, hρ, hmono | hanti⟩ := alg511_edge_curves_orientation f (γ e) hf
      (hγ.cont e he.edge_mem) hfzero hfone hgzero hgone hfinj
      (hγ.inj e he.edge_mem) hfimage (hγ.image e he.edge_mem)
    · let j : Fin m := edge.symm ⟨e, he.edge_mem⟩
      refine ⟨2 * j.val :: ds, ?_, ?_, ?_, j :: labels, ?_, ?_⟩
      · exact ⟨s, has, hstart, hinj, himage, ρ, hρ, Or.inl ⟨rfl, hmono⟩, hds⟩
      · simpa only [List.length_cons, GraphWalk.edges] using congrArg Nat.succ hlen
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · have hj := j.isLt
          omega
        · exact hbound d hd
      · simp only [List.map_cons, hlabels]
        congr 1
        omega
      · change (edge j).val :: labels.map (fun j => (edge j).val) = e :: W.edges
        rw [hedges]
        congr 1
        exact congrArg Subtype.val (edge.apply_symm_apply ⟨e, he.edge_mem⟩)
    · let j : Fin m := edge.symm ⟨e, he.edge_mem⟩
      refine ⟨(2 * j.val + 1) :: ds, ?_, ?_, ?_, j :: labels, ?_, ?_⟩
      · exact ⟨s, has, hstart, hinj, himage, ρ, hρ, Or.inr ⟨rfl, hanti⟩, hds⟩
      · simpa only [List.length_cons, GraphWalk.edges] using congrArg Nat.succ hlen
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · have hj := j.isLt
          omega
        · exact hbound d hd
      · simp only [List.map_cons, hlabels]
        congr 1
        omega
      · change (edge j).val :: labels.map (fun j => (edge j).val) = e :: W.edges
        rw [hedges]
        congr 1
        exact congrArg Subtype.val (edge.apply_symm_apply ⟨e, he.edge_mem⟩)

end GraphMinor.GM06
