module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5TailWalk
import GraphMinor.GM06.Section5Splice
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM11.Walks

/-!
# Replacing a prefix of its own linkage path

For Reduction 4 in VI, page 129, the replacement path starts at the
same initial vertex as the old path. Its only other contact with the
old path is the chosen contact vertex. The old suffix avoids the
start, so it meets the replacement only at the join. Appending their
simple walks gives the new path, also when the suffix is a singleton.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11

/-- Splicing a replacement prefix with its old tail gives a path
under the two-end contact condition of Reduction 4. -/
theorem exists_path_after_own_linkage_tail
    {G P Q : Drawing ClosedCylinder} {s x t : ClosedCylinder}
    (hPG : P.IsSubdrawing G) (hQG : Q.IsSubdrawing G)
    (hP : IsPathDrawing P s t) (hQ : IsPathDrawing Q s x)
    (hx : x ∈ P.V) (hxs : x ≠ s) (hinter : Q.U ∩ P.U ⊆ {s, x}) :
    ∃ T R : Drawing ClosedCylinder,
      IsSection5Tail P T x t ∧ T.IsSubdrawing P ∧
      IsSubpathOf G R s t ∧ R.U = Q.U ∪ T.U := by
  obtain ⟨B, hB, hTail, hsNot⟩ := exists_tail_walk_avoiding_start hP hx hxs
  let T := walkDrawing P B
  have hTP : T.IsSubdrawing P := walkDrawing_isSubdrawing P B
  obtain ⟨W, hW, hVQ, hEQ⟩ := hQ.1
  obtain ⟨A, hAS, hAE⟩ := hQG.exists_walk_up W
  obtain ⟨C, hCS, hCE⟩ := hPG.exists_walk_up B
  have hA : A.IsSimple := by simpa only [GraphWalk.IsSimple, hAS] using hW
  have hC : C.IsSimple := by simpa only [GraphWalk.IsSimple, hCS] using hB
  have hAQ : walkDrawing G A = Q := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hAS, hVQ]
    · rw [walkDrawing_E, hAE, hEQ]
  have hCT : walkDrawing G C = T := by
    apply Drawing.ext_of_V_E
    · simp only [T, walkDrawing_V, hCS]
    · simp only [T, walkDrawing_E, hCE]
  have hwalk : ∀ y ∈ A.support, y ∈ C.support → y = x := by
    intro y hyA hyC
    have hyQ : y ∈ Q.U := by rw [← hAQ, mem_walkDrawing_U]; exact Or.inl hyA
    have hyT : y ∈ T.U := by rw [← hCT, mem_walkDrawing_U]; exact Or.inl hyC
    rcases hinter ⟨hyQ, hTP.U_subset hyT⟩ with hys | hyx
    · exact False.elim (hsNot (hys ▸ hyT))
    · exact hyx
  have hsimple := isSimple_append_at_only_common_vertex A C hA hC hwalk
  have hRG := walkDrawing_isSubdrawing G (A.append C)
  refine ⟨T, walkDrawing G (A.append C), hTail, hTP,
    ⟨hRG, hRG.U_subset, isPathDrawing_walkDrawing_of_isSimple G hsimple (isPathDrawing_start_ne_end hP)⟩, ?_⟩
  rw [walkDrawing_append_U, hAQ, hCT]

end GraphMinor.GM06
