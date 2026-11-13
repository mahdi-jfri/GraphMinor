module

public import GraphMinor.GM06.Defs
import GraphMinor.Surface.Cuffs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.DiscMerge
import GraphMinor.GM11.Walks

/-!
# Comparing enclosed discs near a boundary segment

For Graph Minors VI, Section 4, page 124, two candidate discs have overlapping
interiors near their common boundary segment. We use a small half-plane chart
away from the drawing. Its points off the surface boundary form a connected
set, which lies inside both candidate discs.
-/

public section

namespace GraphMinor.GM06

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- Small neighborhoods in a surface remain connected after removing the
surface boundary. Used near the segment in Graph Minors VI (4.1), page 124. -/
theorem exists_open_nbhd_preconnected_off_bd
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S) (x : S)
    {A : Set S} (hA : IsOpen A) (hxA : x ∈ A) :
    ∃ W : Set S, IsOpen W ∧ x ∈ W ∧ W ⊆ A ∧ IsPreconnected (W \ bd S) := by
  obtain ⟨U, O, j, k, hU, hO, hxU, hj, hk, hjU, hkU, hkj, hjk⟩ := (hS.2.2 x).exists_chart
  have hUA : IsOpen (U ∩ A) := hU.inter hA
  obtain ⟨O₁, hO₁, heq⟩ := continuousOn_iff'.mp hk (U ∩ A) hUA
  have hjx : j x ∈ O ∩ O₁ := by
    refine ⟨(hjU hxU).1, ?_⟩
    have hm : j x ∈ k ⁻¹' (U ∩ A) ∩ (O ∩ halfPlane) := by
      refine ⟨?_, hjU hxU⟩
      rw [mem_preimage, hkj hxU]
      exact ⟨hxU, hxA⟩
    rw [heq] at hm
    exact hm.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hO.inter hO₁) (j x) hjx
  let B : Set ℂ := ball (j x) r ∩ halfPlane
  let C : Set ℂ := ball (j x) r ∩ {z | 0 < z.re}
  let W : Set S := (U ∩ A) ∩ j ⁻¹' ball (j x) r
  have hBO : B ⊆ O ∩ halfPlane := fun z hz => ⟨(hball hz.1).1, hz.2⟩
  have hWO : IsOpen W := (hj.mono inter_subset_left).isOpen_inter_preimage hUA isOpen_ball
  have hxW : x ∈ W := ⟨⟨hxU, hxA⟩, mem_ball_self hr⟩
  have hkB : MapsTo k B W := by
    intro z hz
    have hzpre : z ∈ k ⁻¹' (U ∩ A) ∩ (O ∩ halfPlane) := by
      rw [heq]
      exact ⟨(hball hz.1).2, (hball hz.1).1, hz.2⟩
    refine ⟨hzpre.1, ?_⟩
    change j (k z) ∈ ball (j x) r
    rw [hjk (hBO hz)]
    exact hz.1
  have hCB : C ⊆ B := fun z hz =>
    ⟨hz.1, show 0 ≤ z.re from (show 0 < z.re from hz.2).le⟩
  have hCconv : Convex ℝ C := (convex_ball (j x) r).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm)
  have himage : k '' C = W \ bd S := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      have hyW := hkB (hCB hz)
      refine ⟨hyW, ?_⟩
      intro hyb
      apply hyb
      apply isInteriorPoint_of_chart hU hO hj hk hjU hkU hkj hjk hyW.1.1
      rw [hjk (hBO (hCB hz))]
      exact hz.2
    · intro y hy
      have hyU := hy.1.1.1
      have hre : 0 < (j y).re := by
        by_contra hnot
        have hzero : (j y).re = 0 := le_antisymm (not_lt.mp hnot) (hjU hyU).2
        exact hy.2 (not_isInteriorPoint_of_chart hU hj hjU hkj.injOn hyU hzero)
      exact ⟨j y, ⟨hy.1.2, hre⟩, hkj hyU⟩
  refine ⟨W, hWO, hxW, fun _ hy => hy.1.2, ?_⟩
  rw [← himage]
  exact hCconv.isPreconnected.image k (hk.mono (hCB.trans hBO))

/-- Two enclosed path discs overlap on their insides near the common boundary
segment. This is the local side choice for the minimal path in Graph Minors VI,
Section 4, page 124. -/
theorem enclosed_discs_interior_inter_nonempty
    {S : Type u} [TopologicalSpace S] {G P Q : Drawing S} {A D E : Set S}
    (hS : IsSurface S) (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : P.IsSubdrawing G) (hQ : Q.IsSubdrawing G)
    (hD : IsEnclosedDisc P A D) (hE : IsEnclosedDisc Q A E) :
    (discInt D ∩ discInt E).Nonempty := by
  let : T2Space S := hS.2.1
  obtain ⟨a, ha, heq⟩ := hseg.1
  have haA : a ∈ A := heq ▸ mem_connectedComponentIn ha
  have hAsub : A ⊆ bd S \ (G.V ∩ bd S) := by
    rw [← heq]
    exact connectedComponentIn_subset _ a
  have hclA : closure A ⊆ bd S :=
    closure_minimal (hAsub.trans sdiff_subset) (isClosed_bd S)
  have haGU : a ∉ G.U := by
    intro haU
    exact ha.2 ⟨hG ⟨ha.1, haU⟩, ha.1⟩
  obtain ⟨W, hW, haW, hWU, hconn⟩ :=
    exists_open_nbhd_preconnected_off_bd hS a G.isClosed_U.isOpen_compl haGU
  have hinside : ∀ (R : Drawing S) (B : Set S), R.IsSubdrawing G →
      IsEnclosedDisc R A B → W \ bd S ⊆ discInt B := by
    intro R B hRG hRB
    have haCl : a ∈ closure (discInt B) := hRB.1.subset_closure_discInt (hRB.2.1 haA)
    obtain ⟨z, hzW, hzB⟩ := mem_closure_iff.mp haCl W hW haW
    have hznb : z ∉ bd S := fun hzb =>
      hzb (isInteriorPoint_of_mem_discInt hS.2.2 hRB.1 hzB)
    have hdisj : Disjoint (W \ bd S) (discBd B) := by
      apply disjoint_left.mpr
      intro y hy hyB
      rw [hRB.2.2] at hyB
      rcases hyB with hyR | hyA
      · exact hWU hy.1 (hRG.U_subset hyR)
      · exact hy.2 (hclA hyA)
    rcases hRB.1.side hS.2.2 hconn hdisj with hin | hout
    · exact hin
    · exact False.elim (disjoint_left.mp hout ⟨hzW, hznb⟩ hzB.1)
  have haCl : a ∈ closure (discInt D) := hD.1.subset_closure_discInt (hD.2.1 haA)
  obtain ⟨z, hzW, hzD⟩ := mem_closure_iff.mp haCl W hW haW
  have hznb : z ∉ bd S := fun hzb => hzb (isInteriorPoint_of_mem_discInt hS.2.2 hD.1 hzD)
  exact ⟨z, hinside P D hP hD ⟨hzW, hznb⟩, hinside Q E hQ hE ⟨hzW, hznb⟩⟩

/-- A competing path that avoids the inside of an enclosed path disc must
leave that whole disc on its segment side. This is the last side comparison
for the minimal path in Graph Minors VI, Section 4, page 124. -/
theorem enclosedDisc_subset_of_disjoint_path_discInt
    {S : Type u} [TopologicalSpace S] {G P Q : Drawing S} {A D E : Set S}
    (hS : IsSurface S) (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : P.IsSubdrawing G) (hQ : Q.IsSubdrawing G)
    (hD : IsEnclosedDisc P A D) (hE : IsEnclosedDisc Q A E)
    (havoid : Disjoint Q.U (discInt D)) : D ⊆ E := by
  let : T2Space S := hS.2.1
  have hAsub : A ⊆ bd S := by
    obtain ⟨a, ha, heq⟩ := hseg.1
    rw [← heq]
    exact (connectedComponentIn_subset _ a).trans sdiff_subset
  have hclA : closure A ⊆ bd S := closure_minimal hAsub (isClosed_bd S)
  have hdisj : Disjoint (discInt D) (discBd E) := by
    apply disjoint_left.mpr
    intro x hx hxE
    rw [hE.2.2] at hxE
    rcases hxE with hxQ | hxA
    · exact disjoint_left.mp havoid hxQ hx
    · exact hclA hxA (isInteriorPoint_of_mem_discInt hS.2.2 hD.1 hx)
  have hmeet := enclosed_discs_interior_inter_nonempty hS hG hseg hP hQ hD hE
  have hin : discInt D ⊆ discInt E := by
    rcases hE.1.side hS.2.2 hD.1.isPreconnected_discInt hdisj with h | h
    · exact h
    · obtain ⟨x, hxD, hxE⟩ := hmeet
      exact False.elim (disjoint_left.mp h hxD hxE.1)
  exact hD.1.subset_closure_discInt.trans
    (closure_minimal (hin.trans (discInt_subset E)) hE.1.isClosed)

end GraphMinor.GM06
