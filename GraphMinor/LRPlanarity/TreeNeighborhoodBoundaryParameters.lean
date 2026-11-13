module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.SurfaceGraph
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Parameter intervals of attachment arcs

Part IV, Section 7b of the planarity note replaces one boundary interval
by a child detour. For a traversal cut outside that interval, its parameters
form one closed interval strictly inside the unit interval. Compactness
gives the first and last parameters. The traversal between them is an
embedding, so connectedness of the attachment arc fills every parameter
between those extrema.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface Topology

/-- Part IV, Section 7b: a closed attachment arc avoiding both ends of a
boundary traversal occupies one nondegenerate interior parameter interval. -/
theorem exists_boundary_arc_parameter_interval {C L : Set ℂ} {a b : ℂ}
    (hL : IsLineWithEnds L a b) (hsub : L ⊆ C) (f : ℝ → ℂ) (hf : Continuous f)
    (hinj : InjOn f (Ico (0 : ℝ) 1)) (himage : f '' Icc (0 : ℝ) 1 = C)
    (hzero : f 0 ∉ L) (hone : f 1 ∉ L) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ hi < 1 ∧ f '' Icc lo hi = L := by
  let K : Set ℝ := Icc (0 : ℝ) 1 ∩ f ⁻¹' L
  have hclosedL : IsClosed L := hL.isCompact.isClosed
  have hK : IsCompact K := isCompact_Icc.inter_right (hclosedL.preimage hf)
  have hKne : K.Nonempty := by
    obtain ⟨t,ht,he⟩ := himage.symm ▸ hsub hL.left_mem
    exact ⟨t,ht,(show f t ∈ L from he.symm ▸ hL.left_mem)⟩
  obtain ⟨lo,hlo,hmin⟩ := hK.exists_isLeast hKne
  obtain ⟨hi,hhi,hmax⟩ := hK.exists_isGreatest hKne
  have hlo0 : 0 < lo := lt_of_le_of_ne hlo.1.1 (fun he => hzero (he.symm ▸ hlo.2))
  have hhi1 : hi < 1 := lt_of_le_of_ne hhi.1.2 (fun he => hone (he ▸ hhi.2))
  have hlohi : lo ≤ hi := hmin hhi
  let g : Icc lo hi → ℂ := fun t => f t.val
  have hg : Continuous g := hf.comp continuous_subtype_val
  have hginj : Function.Injective g := by
    intro x y he
    apply Subtype.ext
    exact hinj ⟨hlo0.le.trans x.property.1,x.property.2.trans_lt hhi1⟩
      ⟨hlo0.le.trans y.property.1,y.property.2.trans_lt hhi1⟩ he
  have hemb : IsEmbedding g := (hg.isClosedEmbedding hginj).isEmbedding
  have hLrange : L ⊆ range g := by
    intro x hx
    obtain ⟨t,ht,he⟩ := himage.symm ▸ hsub hx
    have htK : t ∈ K := ⟨ht,(show f t ∈ L from he.symm ▸ hx)⟩
    exact ⟨⟨t,⟨hmin htK,hmax htK⟩⟩,he⟩
  have hLpc : IsPreconnected L := by
    obtain ⟨k,hk,hrange,_,_⟩ := hL.exists_arc
    rw [← hrange]
    exact isPreconnected_range hk.1
  have hpre : IsPreconnected (g ⁻¹' L) := by
    apply hemb.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_inter_range,inter_eq_left.mpr hLrange]
    exact hLpc
  have hKimage : (Subtype.val : Icc lo hi → ℝ) '' (g ⁻¹' L) = K := by
    apply Subset.antisymm
    · rintro t ⟨x,hx,rfl⟩
      exact ⟨⟨hlo0.le.trans x.property.1,x.property.2.trans hhi1.le⟩,hx⟩
    · intro t ht
      exact ⟨⟨t,⟨hmin ht,hmax ht⟩⟩,ht.2,rfl⟩
  have hKpc : IsPreconnected K := by
    rw [← hKimage]
    exact hpre.image Subtype.val continuous_subtype_val.continuousOn
  have hinterval : Icc lo hi ⊆ K := fun _ ht => hKpc.ordConnected.out hlo hhi ht
  have heq : f '' Icc lo hi = L := by
    apply Subset.antisymm
    · rintro x ⟨t,ht,rfl⟩
      exact (hinterval ht).2
    · intro x hx
      obtain ⟨t,ht⟩ := hLrange hx
      exact ⟨t.val,t.property,ht⟩
  have hstrict : lo < hi := lt_of_le_of_ne hlohi (by
    intro hsame
    have hsingle : ∀ x ∈ L, x = f lo := by
      intro x hx
      obtain ⟨t,ht,rfl⟩ := heq.symm ▸ hx
      have htlo : t = lo := le_antisymm (ht.2.trans hsame.symm.le) ht.1
      exact congrArg f htlo
    obtain ⟨k,hk,_,hk0,hk1⟩ := hL.exists_arc
    have hab : a = b := (hsingle a hL.left_mem).trans (hsingle b hL.right_mem).symm
    exact zero_ne_one (hk.2 (hk0.trans (hab.trans hk1.symm))))
  exact ⟨lo,hi,hlo0,hstrict,hhi1,heq⟩

end GraphMinor.LRPlanarity
