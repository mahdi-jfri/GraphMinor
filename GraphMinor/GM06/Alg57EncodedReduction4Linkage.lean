module

public import GraphMinor.GM06.Alg57ComputedWalkEncoding
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction

/-!
# An encoded Reduction 4 replacement linkage

The splice in VI (5.7), page 133, replaces one path and preserves
all other paths. Here the replacement is a given simple graph walk
with its actual directed word row. Parametrizing its drawing gives
the required cylinder linkage. The new row encoding uses that same
walk and the unchanged encoded walks for the other indices.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- The Reduction 4 splice preserves the exact encoded replacement
row, as well as giving the geometric reduction step. All the
hypotheses describe the local prefix, candidate and retained tail. -/
theorem exists_encoded_reduction4_linkage {n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hk : 1 < k) (i : Fin k)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (rows : List (List ℕ)) (row : List ℕ)
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    {v : ClosedCylinder} (hv : v ∈ (L.pathDrawing i).V)
    (hvR : v ∈ closure (cylinderRegion k G i))
    {P_sv : Drawing ClosedCylinder} (hsv : IsSubpathOf (L.pathDrawing i) P_sv (cylinderM1Point k i) v)
    (hpre : ¬ P_sv.U ⊆ closure (cylinderRegion k G i))
    {T : Drawing ClosedCylinder} (hT : IsSection5Tail (L.pathDrawing i) T v (L.curve i 1))
    {Q : Drawing ClosedCylinder} (hQG : Q.IsSubdrawing G)
    (hQ : IsPathDrawing Q (cylinderM1Point k i) v)
    (hQR : Q.U ⊆ closure (cylinderRegion k G i))
    (hQP : ∀ j, j ≠ i → Disjoint Q.U (L.pathDrawing j).U)
    (W : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve i 1))
    (hW : W.IsSimple) (henc : GM06WalkDartEncoding G.toGraph tagged vertex edge W row)
    (hRU : (walkDrawing G W).U = Q.U ∪ T.U) :
    ∃ L' : CylinderLinkage k G, Section5Reduction4Step k G L G L' ∧
      GM06LinkageRowsEncoding L' tagged vertex edge (rows.set i.val row) := by
  classical
  let R := walkDrawing G W
  have hRG : R.IsSubdrawing G := walkDrawing_isSubdrawing G W
  have hR : IsPathDrawing R (cylinderM1Point k i) (L.curve i 1) :=
    isPathDrawing_walkDrawing_of_isSimple G hW (isPathDrawing_start_ne_end (L.isPath i))
  obtain ⟨f, hf⟩ := hR.2
  have hTU : T.U ⊆ (L.pathDrawing i).U := by
    rcases hT with ⟨rfl, hTU, -⟩ | ⟨-, hTU, -⟩
    · rw [hTU]
      exact singleton_subset_iff.mpr ((L.pathDrawing i).V_subset_U hv)
    · exact hTU
  let P' : Fin k → Drawing ClosedCylinder := fun j => if j = i then R else L.pathDrawing j
  let c' : Fin k → Curve ClosedCylinder := fun j => if j = i then f else L.curve j
  have hP'i : P' i = R := by simp only [P', ↓reduceIte]
  have hc'i : c' i = f := by simp only [c', ↓reduceIte]
  have hP'j : ∀ j, j ≠ i → P' j = L.pathDrawing j := fun j hj => by simp only [P', hj, ↓reduceIte]
  have hc'j : ∀ j, j ≠ i → c' j = L.curve j := fun j hj => by simp only [c', hj, ↓reduceIte]
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
  have hStep : Section5Reduction4Step k G L G L' := by
    refine ⟨rfl, Or.inl ⟨hk, ?_⟩⟩
    refine ⟨i, v, P_sv, T, Q, hv, hvR, hsv, hT, hpre, hQG, hQG.U_subset, hQ, hQR, ?_, ?_⟩
    · change (P' i).U = _
      rw [hP'i, hRU]
    · intro j hj
      exact ⟨hP'j j hj, hc'j j hj⟩
  refine ⟨L', hStep, ?_⟩
  have hlen : (rows.set i.val row).length = k := by rw [List.length_set, hrows.1]
  refine ⟨hlen, fun j => ?_⟩
  have hjlen : j.val < rows.length := hrows.1.symm ▸ j.isLt
  rw [List.getElem?_eq_getElem (hlen.symm ▸ j.isLt), Option.getD_some]
  by_cases hj : j = i
  · subst j
    rw [List.getElem_set_self]
    change ∃ A : GraphWalk G.toGraph (cylinderM1Point k i) (c' i 1),
      A.IsSimple ∧ GM06WalkDartEncoding G.toGraph tagged vertex edge A row ∧ walkDrawing G A = P' i
    rw [hc'i, hf.2.2.2, hP'i]
    exact ⟨W, hW, henc, rfl⟩
  · have hne : i.val ≠ j.val := fun h => hj (Fin.ext h.symm)
    rw [List.getElem_set_ne hne]
    change ∃ A : GraphWalk G.toGraph (cylinderM1Point k j) (c' j 1),
      A.IsSimple ∧ GM06WalkDartEncoding G.toGraph tagged vertex edge A rows[j.val] ∧
      walkDrawing G A = P' j
    rw [hc'j j hj, hP'j j hj]
    exact hrows.path j

end GraphMinor.GM06
