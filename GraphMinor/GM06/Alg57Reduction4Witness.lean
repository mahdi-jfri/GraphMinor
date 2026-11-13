module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Splice
import GraphMinor.GM06.Section5TailWalk
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# A path found by `FIND_4` gives Reduction 4

This is the soundness half of Lemma 13 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`)
for `k ≥ 2`, at the level of drawings. `FIND_4` returns a path `Q` from `sᵢ` to a vertex `v` of
`Pᵢ`. It is found in the graph `A_{i,j}`, so it lies in the closure of `Rᵢ`, misses the other
linkage paths, and meets the tail of `Pᵢ` after `v` only at `v`. The prefix test says that the
subpath of `Pᵢ` from `sᵢ` to `v` does not lie in the closure of `Rᵢ`.

We show that these facts give Reduction 4 in the printed form of VI, page 129
(`section5AnyReductionApplies_of_reduction4_path`). The new path `Q · Pᵢ[v, tᵢ]` is a path,
because `Q` and the tail are paths that share only `v` (`isSimple_append_at_only_common_vertex`).
It misses the other paths because `Q` does and the tail lies in `Pᵢ`. So replacing `Pᵢ` by it gives
a linkage, and the drawing is unchanged.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

/-- The path `Q · T` for a path `Q` from `s` to `v` and a Reduction 4 tail `T` from `v` to `t`
that meets `Q` only at `v`. -/
theorem exists_path_append_tail {G P Q T : Drawing ClosedCylinder} {s v t : ClosedCylinder}
    (hPG : P.IsSubdrawing G) (hQG : Q.IsSubdrawing G) (hQ : IsPathDrawing Q s v)
    (hT : IsSection5Tail P T v t) (hst : s ≠ t) (hQT : Q.U ∩ T.U ⊆ {v}) :
    ∃ R : Drawing ClosedCylinder, R.IsSubdrawing G ∧ IsPathDrawing R s t ∧
      R.U = Q.U ∪ T.U := by
  have hvQ : v ∈ Q.U := Q.V_subset_U (isPathDrawing_end_vertices hQ).2
  rcases hT with ⟨rfl, hTU, -⟩ | ⟨hTP, -, hTpath⟩
  · refine ⟨Q, hQG, hQ, ?_⟩
    rw [hTU, union_eq_left.mpr (singleton_subset_iff.mpr hvQ)]
  · obtain ⟨W, hW, hVQ, hEQ⟩ := hQ.1
    obtain ⟨B, hB, hVT, hET⟩ := hTpath.1
    obtain ⟨A, hAS, hAE⟩ := hQG.exists_walk_up W
    obtain ⟨C, hCS, hCE⟩ := (hTP.trans hPG).exists_walk_up B
    have hA : A.IsSimple := by simpa only [GraphWalk.IsSimple, hAS] using hW
    have hC : C.IsSimple := by simpa only [GraphWalk.IsSimple, hCS] using hB
    have hAQ : walkDrawing G A = Q := by
      apply Drawing.ext_of_V_E
      · rw [walkDrawing_V, hAS, hVQ]
      · rw [walkDrawing_E, hAE, hEQ]
    have hCT : walkDrawing G C = T := by
      apply Drawing.ext_of_V_E
      · rw [walkDrawing_V, hCS, hVT]
      · rw [walkDrawing_E, hCE, hET]
    have hwalk : ∀ y ∈ A.support, y ∈ C.support → y = v := by
      intro y hyA hyC
      have hyQ : y ∈ Q.U := by
        rw [← hAQ, mem_walkDrawing_U]
        exact Or.inl hyA
      have hyT : y ∈ T.U := by
        rw [← hCT, mem_walkDrawing_U]
        exact Or.inl hyC
      exact mem_singleton_iff.mp (hQT ⟨hyQ, hyT⟩)
    have hsimple := isSimple_append_at_only_common_vertex A C hA hC hwalk
    refine ⟨walkDrawing G (A.append C), walkDrawing_isSubdrawing G _,
      isPathDrawing_walkDrawing_of_isSimple G hsimple hst, ?_⟩
    rw [walkDrawing_append_U, hAQ, hCT]

/-- **Lemma 13, soundness, for `k ≥ 2`, as a Reduction 4 step.** Let `v` be a vertex of `Pᵢ`
in the closure of `Rᵢ`,
such that the subpath of `Pᵢ` from `sᵢ` to `v` does not lie in that closure. Let `Q` be a path of
`G` from `sᵢ` to `v` in the closure of `Rᵢ`, which misses the other linkage paths and meets the
tail of `Pᵢ` from `v` only at `v`. Then Reduction 4 applies, with the drawing unchanged. -/
theorem exists_reduction4Step_of_path {k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hk : 1 < k) (i : Fin k)
    {v : ClosedCylinder} (hv : v ∈ (L.pathDrawing i).V)
    (hvR : v ∈ closure (cylinderRegion k G i))
    {P_sv : Drawing ClosedCylinder} (hsv : IsSubpathOf (L.pathDrawing i) P_sv (cylinderM1Point k i) v)
    (hpre : ¬ P_sv.U ⊆ closure (cylinderRegion k G i))
    {T : Drawing ClosedCylinder} (hT : IsSection5Tail (L.pathDrawing i) T v (L.curve i 1))
    {Q : Drawing ClosedCylinder} (hQG : Q.IsSubdrawing G)
    (hQ : IsPathDrawing Q (cylinderM1Point k i) v)
    (hQR : Q.U ⊆ closure (cylinderRegion k G i)) (hQT : Q.U ∩ T.U ⊆ {v})
    (hQP : ∀ j, j ≠ i → Disjoint Q.U (L.pathDrawing j).U) :
    ∃ L' : CylinderLinkage k G, Section5Reduction4Step k G L G L' := by
  classical
  have hst : cylinderM1Point k i ≠ L.curve i 1 := isPathDrawing_start_ne_end (L.isPath i)
  obtain ⟨R, hRG, hR, hRU⟩ :=
    exists_path_append_tail (L.isSubdrawing i).1 hQG hQ hT hst hQT
  obtain ⟨f, hf⟩ := hR.2
  have hTU : T.U ⊆ (L.pathDrawing i).U := by
    rcases hT with ⟨rfl, hTU, -⟩ | ⟨-, hTU, -⟩
    · rw [hTU]
      exact singleton_subset_iff.mpr ((L.pathDrawing i).V_subset_U hv)
    · exact hTU
  let P' : Fin k → Drawing ClosedCylinder := fun j => if j = i then R else L.pathDrawing j
  let c' : Fin k → Curve ClosedCylinder := fun j => if j = i then f else L.curve j
  have hP'i : P' i = R := if_pos rfl
  have hc'i : c' i = f := if_pos rfl
  have hP'j : ∀ j, j ≠ i → P' j = L.pathDrawing j := fun j hj => if_neg hj
  have hc'j : ∀ j, j ≠ i → c' j = L.curve j := fun j hj => if_neg hj
  have hRdisj : ∀ j, j ≠ i → Disjoint R.U (L.pathDrawing j).U := by
    intro j hj
    rw [hRU]
    exact Disjoint.union_left (hQP j hj)
      ((L.pairwise_disjoint (Ne.symm hj)).mono_left hTU)
  let L' : CylinderLinkage k G := {
    pathDrawing := P'
    curve := c'
    isSubdrawing j := by
      by_cases hj : j = i
      · subst hj
        rw [hP'i]
        exact ⟨hRG, hRG.U_subset⟩
      · rw [hP'j j hj]
        exact L.isSubdrawing j
    isPath j := by
      by_cases hj : j = i
      · subst hj
        rw [hP'i, hc'i, hf.2.2.2]
        exact hR
      · rw [hP'j j hj, hc'j j hj]
        exact L.isPath j
    curve_parametrizes j := by
      by_cases hj : j = i
      · subst hj
        rw [hP'i, hc'i, hf.2.2.2]
        exact hf
      · rw [hP'j j hj, hc'j j hj]
        exact L.curve_parametrizes j
    curve_one_mem j := by
      by_cases hj : j = i
      · subst hj
        rw [hc'i, hf.2.2.2]
        exact L.curve_one_mem j
      · rw [hc'j j hj]
        exact L.curve_one_mem j
    pairwise_disjoint := by
      intro a b hab
      by_cases ha : a = i
      · subst ha
        rw [hP'i, hP'j b (Ne.symm hab)]
        exact hRdisj b (Ne.symm hab)
      · by_cases hb : b = i
        · subst hb
          rw [hP'i, hP'j a hab]
          exact (hRdisj a hab).symm
        · rw [hP'j a ha, hP'j b hb]
          exact L.pairwise_disjoint hab }
  refine ⟨L', rfl, Or.inl ⟨hk, ?_⟩⟩
  refine ⟨i, v, P_sv, T, Q, hv, hvR, hsv, hT, hpre, hQG, hQG.U_subset, hQ, hQR, ?_, ?_⟩
  · change (P' i).U = _
    rw [hP'i, hRU]
  · intro j hj
    exact ⟨hP'j j hj, hc'j j hj⟩

/-- **Lemma 13, soundness, for `k ≥ 2`**, as the statement that some reduction applies. -/
theorem section5AnyReductionApplies_of_reduction4_path {k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {v : ClosedCylinder} (hv : v ∈ (L.pathDrawing i).V)
    (hvR : v ∈ closure (cylinderRegion k G i))
    {P_sv : Drawing ClosedCylinder} (hsv : IsSubpathOf (L.pathDrawing i) P_sv (cylinderM1Point k i) v)
    (hpre : ¬ P_sv.U ⊆ closure (cylinderRegion k G i))
    {T : Drawing ClosedCylinder} (hT : IsSection5Tail (L.pathDrawing i) T v (L.curve i 1))
    {Q : Drawing ClosedCylinder} (hQG : Q.IsSubdrawing G)
    (hQ : IsPathDrawing Q (cylinderM1Point k i) v)
    (hQR : Q.U ⊆ closure (cylinderRegion k G i)) (hQT : Q.U ∩ T.U ⊆ {v})
    (hQP : ∀ j, j ≠ i → Disjoint Q.U (L.pathDrawing j).U) :
    Section5AnyReductionApplies k G L := by
  obtain ⟨L', h⟩ := exists_reduction4Step_of_path L hk i hv hvR hsv hpre hT hQG hQ hQR hQT hQP
  exact ⟨G, L', hG, Or.inr (Or.inr (Or.inr h))⟩

end GraphMinor.GM06
