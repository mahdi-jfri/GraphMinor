module

public import GraphMinor.Compute.GM06PullbackWalkEncoding
public import GraphMinor.Compute.GM06LinkageRowsEncoding
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4

/-!
# Recovering the output linkage after one contraction

VI (5.7), page 133, returns a linkage when the next winding is
feasible. To reverse Reduction 3, lift its encoded paths through
the collapse. Only the path starting at the contracted vertex
needs the recorded initial word restored. The other paths retain
their words. Their images are the disjoint new paths, so the old
paths are disjoint too. The boundary-fixing homotopy preserves
winding. Thus the concrete one-row recovery update encodes an
actual old linkage of exactly the returned winding.
-/

public section
namespace GraphMinor.Compute
open Set Topology GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

/-- Restoring the recorded initial directed word to its path row
recovers a linkage in the old drawing with the same winding. -/
theorem gm06LinkageRowsEncoding_expand
    {n k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k} {θ : ℝ}
    (hG : IsCylinderSection5Drawing k G)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex vertex' : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hLive : ∀ x, vertex x ∈ G.V → x ∈ A)
    (a b : Fin n) (ha : a ∈ A) (hab : a ≠ b)
    (hpoint : vertex a = cylinderM1Point k i) (d₀ : Fin tagged.length) (hd₀ : tagged[d₀].2 = 1)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d₀) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure (edge d₀)) (hi : InjOn π (closure (edge d₀))ᶜ)
    (hV : G'.V = π '' G.V)
    (hnew : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (hH0 : ∀ x, H (0, x) = x) (hH1 : ∀ x, H (1, x) = π x)
    (hHbd : ∀ x ∈ bd ClosedCylinder, ∀ t, H (t, x) = x)
    (first : ℕ) (hfirst : first < 2 * tagged.length) (hfirstEdge : first / 2 = d₀.val)
    (hfirstTail : vertex (gm06DartTail tagged ⟨first, hfirst⟩) = cylinderM1Point k i)
    (hfirstHead : vertex (gm06DartHead tagged ⟨first, hfirst⟩) = vertex b)
    (M : CylinderLinkage k G') (hθ : M.HasTheta θ) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M (gm06ContractTaggedEdges tagged a b d₀.val) vertex'
      (fun j => π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) j)) rows) :
    ∃ N : CylinderLinkage k G, N.HasTheta θ ∧
      GM06LinkageRowsEncoding N tagged vertex edge
        (rows.set i.val (first :: (rows[i.val]?.getD []))) := by
  classical
  let D := G.V \ {cylinderM1Point k i}
  let J := induceDrawing G D
  have hJV : J.V = D := induceDrawing_V G sdiff_subset
  have hDi : InjOn π D :=
    (injOn_deleted_initial_vertex_drawing hval hl hvs hfiber hi).mono
      (by intro x hx; exact J.V_subset_U (hJV.symm ▸ hx))
  have hbd : ∀ x ∈ bd ClosedCylinder, π x = x :=
    fun x hx => (hH1 x).symm.trans (hHbd x hx 1)
  have hπb : π (vertex b) = cylinderM1Point k i := by
    have hx : vertex b ∈ closure (edge d₀) :=
      (show vertex b ∈ closure (edge d₀) ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
    have hx' : vertex b ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hx
    exact hx'
  have hex (j : Fin k) : ∃ R : GraphWalk G.toGraph (cylinderM1Point k j) (M.curve j 1),
      R.IsSimple ∧ GM06WalkDartEncoding G.toGraph tagged vertex edge R
        (if j = i then first :: (rows[j.val]?.getD []) else rows[j.val]?.getD []) ∧
      π '' (walkDrawing G R).U = (M.pathDrawing j).U := by
    obtain ⟨W, hW, henc, hP⟩ := hrows.2 j
    obtain ⟨x, hx, y, hy, R, hR, hencR, hπx, hπy, hs, he, hRD⟩ :=
      exists_expanded_encoded_walk tagged vertex vertex' edge A hinj hlinks hLive a b ha hab hpoint
        d₀ hd₀ hval hl hvs π hfiber hi hV hnew W (rows[j.val]?.getD []) hW henc
    have htC : M.curve j 1 ∈ cylinderCuff2 := by
      obtain ⟨l, hle⟩ := M.curve_one_mem j
      exact hle ▸ cylinderM2Point_mem_cylinderCuff2 k l
    have htbd : M.curve j 1 ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inr htC
    have htG : M.curve j 1 ∈ G.V :=
      ((hG.2.2).symm ▸ (show M.curve j 1 ∈ cylinderM1 k ∪ cylinderM2 k from Or.inr (M.curve_one_mem j))).1
    have htD : M.curve j 1 ∈ D :=
      ⟨htG, disjoint_cylinderCuffs.symm.ne_of_mem htC (cylinderM1Point_mem_cylinderCuff1 k i)⟩
    have hyt : y = M.curve j 1 := hDi hy htD (hπy.trans (hbd _ htbd).symm)
    cases hyt
    have hRU : π '' (walkDrawing G R).U = (M.pathDrawing j).U :=
      (walkDrawing_image_pointSet π R W hs.symm he.symm).symm.trans (congrArg Drawing.U hP)
    by_cases hji : j = i
    · subst j
      have hxb : x = vertex b := hDi hx ⟨hl.right_mem, hvs⟩ (hπx.trans hπb.symm)
      cases hxb
      have hsnot : cylinderM1Point k i ∉ R.support := fun hp => (hRD _ hp).2 rfl
      have hsimple : (GraphWalk.cons hl R).IsSimple := List.nodup_cons.mpr ⟨hsnot, hR⟩
      have hflag : (tagged[first / 2]'(by omega)).2 = 1 := by
        simpa only [hfirstEdge, Fin.getElem_fin] using hd₀
      have hedge : edge ⟨first / 2, by omega⟩ = edge d₀ := congrArg edge (Fin.ext hfirstEdge)
      refine ⟨.cons hl R, hsimple, ?_, ?_⟩
      · simp only [ite_true]
        exact .cons hfirst hflag hedge hfirstTail hfirstHead hencR
      · rw [walkDrawing_cons_pointSet, image_union, hRU]
        have hcl : π '' closure (edge d₀) = {cylinderM1Point k i} := by
          apply subset_antisymm
          · rintro z ⟨q, hq, rfl⟩
            have hq' : q ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hq
            exact hq'
          · rintro z rfl
            refine ⟨vertex b, ?_, hπb⟩
            exact (show vertex b ∈ closure (edge d₀) ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
        rw [hcl]
        apply union_eq_right.mpr
        apply singleton_subset_iff.mpr
        rw [← (M.curve_parametrizes i).2.1]
        exact ⟨0, (M.curve_parametrizes i).2.2.1⟩
    · have hsne := (cylinderM1Point_injective hG.1).ne hji
      have hsG : cylinderM1Point k j ∈ G.V :=
        ((hG.2.2).symm ▸ (show cylinderM1Point k j ∈ cylinderM1 k ∪ cylinderM2 k from Or.inl ⟨j, rfl⟩)).1
      have hxs : x = cylinderM1Point k j := hDi hx ⟨hsG, hsne⟩
        (hπx.trans (hbd _ (cylinderM1Point_mem_bd k j)).symm)
      cases hxs
      exact ⟨R, hR, by simpa only [hji, ite_false] using hencR, hRU⟩
  choose W hsimple henc hWU using hex
  have hparam (j : Fin k) : ∃ f : Curve ClosedCylinder,
      ParametrizesSet f (walkDrawing G (W j)).U (cylinderM1Point k j) (M.curve j 1) := by
    apply exists_parametrizesSet_walkDrawing_of_isSimple G (hsimple j)
    obtain ⟨l, hl⟩ := M.curve_one_mem j
    exact disjoint_cylinderCuffs.ne_of_mem (cylinderM1Point_mem_cylinderCuff1 k j)
      (hl ▸ cylinderM2Point_mem_cylinderCuff2 k l)
  choose f hf using hparam
  have hwind (j : Fin k) : windingNumber (f j) = θ := by
    have hsbd : f j 0 ∈ bd ClosedCylinder := (hf j).2.2.1.symm ▸ cylinderM1Point_mem_bd k j
    have htbd : f j 1 ∈ bd ClosedCylinder := by
      rw [(hf j).2.2.2]
      obtain ⟨l, hl⟩ := M.curve_one_mem j
      exact hl ▸ cylinderM2Point_mem_bd k l
    have hhom1 := curvesHomotopic_comp_pi_map hH0 hH1 hHbd hsbd htbd
    have hsub : range (π.comp (f j)) ⊆ (M.pathDrawing j).U := by
      rintro z ⟨t, rfl⟩
      rw [← hWU j]
      refine ⟨f j t, ?_, rfl⟩
      rw [← (hf j).2.1]
      exact mem_range_self t
    have hstart : (π.comp (f j)) 0 = cylinderM1Point k j := by
      change π (f j 0) = _
      rw [(hf j).2.2.1, hbd _ (cylinderM1Point_mem_bd k j)]
    have hend : (π.comp (f j)) 1 = M.curve j 1 := by
      change π (f j 1) = _
      rw [hbd _ htbd, (hf j).2.2.2]
    have hhom2 := curvesHomotopicIn_of_range_subset_parametrizesSet (M.curve_parametrizes j) hsub hstart hend
    have hhom2' : CurvesHomotopic (π.comp (f j)) (M.curve j) := by
      obtain ⟨K, _, h0, h1, hs0, hs1, ht0, ht1⟩ := hhom2
      exact ⟨K, fun _ => trivial, h0, h1, hs0, hs1, ht0, ht1⟩
    rw [windingNumber_eq_of_homotopic hhom1, windingNumber_eq_of_homotopic hhom2', hθ j]
  let N : CylinderLinkage k G := {
    pathDrawing := fun j => walkDrawing G (W j)
    curve := f
    isSubdrawing := fun j => ⟨walkDrawing_isSubdrawing G (W j), (walkDrawing_isSubdrawing G (W j)).U_subset⟩
    isPath := fun j => by
      rw [(hf j).2.2.2]
      exact ⟨walkDrawing_isPathBetween G (hsimple j), ⟨f j, hf j⟩⟩
    curve_parametrizes := fun j => ⟨(hf j).1, (hf j).2.1, (hf j).2.2.1, rfl⟩
    curve_one_mem := fun j => by rw [(hf j).2.2.2]; exact M.curve_one_mem j
    pairwise_disjoint := fun j l hjl => by
      apply disjoint_left.mpr
      intro x hxj hxl
      exact disjoint_left.mp (M.pairwise_disjoint hjl)
        (hWU j ▸ mem_image_of_mem π hxj) (hWU l ▸ mem_image_of_mem π hxl) }
  refine ⟨N, hwind, by simpa only [List.length_set] using hrows.1, ?_⟩
  intro j
  have hrow : (rows.set i.val (first :: (rows[i.val]?.getD [])))[j.val]?.getD [] =
      (if j = i then first :: (rows[j.val]?.getD []) else rows[j.val]?.getD []) := by
    by_cases hji : j = i
    · subst j
      simp only [List.getElem?_set_self (show i.val < rows.length by rw [hrows.1]; exact i.isLt),
        Option.getD_some, ite_true]
    · rw [List.getElem?_set_ne (show i.val ≠ j.val from fun h => hji (Fin.ext h.symm))]
      simp only [hji, ite_false]
  rw [hrow]
  have hend : f j 1 = M.curve j 1 := (hf j).2.2.2
  change ∃ R : GraphWalk G.toGraph (cylinderM1Point k j) (f j 1), R.IsSimple ∧
    GM06WalkDartEncoding G.toGraph tagged vertex edge R _ ∧ walkDrawing G R = walkDrawing G (W j)
  rw [hend]
  exact ⟨W j, hsimple j, henc j, rfl⟩

end GraphMinor.Compute
