module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5InitialRegionEdge
import GraphMinor.GM06.Section5ProperPaths
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM11.Walks

/-!
# The single edge in the base case of (5.3)

A valency-one start forces the first edge of its linkage walk. If its
neighbour is on the outer cuff, properness makes it the terminal vertex.
The region-edge assertion then puts this edge in the initial region closure.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11
private theorem path_eq_closed_edge_of_forced_first_link {G P : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (hPG : P.IsSubdrawing G)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hforced : ∀ e ∈ G.E, e ≠ a → s ∉ closure e)
    (hl : G.toGraph.IsLink a s v)
    (hterminal : v ∈ P.U → v = t) :
    v = t ∧ P.U = closure a := by
  have hvcl : v ∈ closure a :=
    (show v ∈ closure a ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem s rfl).1
  obtain ⟨W, hW, hV, hE⟩ := hP.1
  cases W with
  | nil _ => exact False.elim ((isPathDrawing_start_ne_end hP) rfl)
  | @cons s w t e hlink R =>
    have hlinkG := (hPG.isLink_iff hlink.1).mp hlink
    have hscl : s ∈ closure e :=
      (show s ∈ closure e ∩ G.V from hlinkG.2.2.2.symm ▸ mem_insert s {w}).1
    have hea : e = a := by
      by_contra hne
      exact hforced e hlinkG.1 hne hscl
    have hwne : w ≠ s := by
      intro hws
      exact (List.nodup_cons.mp hW).1 (hws ▸ R.start_mem_support)
    have hwv : w = v := by
      have hp : ({s, w} : Set ClosedCylinder) = {s, v} :=
        hlinkG.2.2.2.symm.trans (hea.symm ▸ hl.2.2.2)
      have hw : w ∈ ({s, v} : Set ClosedCylinder) := hp ▸ mem_insert_of_mem s rfl
      rcases hw with hws | hwv
      · exact False.elim (hwne hws)
      · exact hwv
    subst w
    have hvU : v ∈ P.U := by
      apply P.V_subset_U
      rw [hV]
      exact List.mem_cons_of_mem s R.start_mem_support
    have hvt : v = t := hterminal hvU
    subst v
    have hz := GraphWalk.IsSimple.length_eq_zero (List.nodup_cons.mp hW).2
    cases R with
    | nil ht =>
      refine ⟨rfl, ?_⟩
      rw [P.U_eq]
      have hverts : P.V ⊆ closure a := by
        rw [hV]
        intro x hx
        simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hea ▸ hscl
        · exact hvcl
      have hedges : P.E = {a} := by
        rw [hE]
        simp only [GraphWalk.edges, hea, List.mem_singleton]
        rfl
      simp only [hedges, mem_singleton_iff, iUnion_iUnion_eq_left]
      exact union_eq_right.mpr hverts
    | cons _ _ => simp [GraphWalk.length, GraphWalk.edges] at hz
/-- The single-edge assertion in the base case of VI (5.3), page 132. -/
theorem linkage_path_eq_closed_edge_of_valency_one {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvC : v ∈ cylinderCuff2) :
    v = L.curve i 1 ∧ (L.pathDrawing i).U = closure a := by
  have hvs : v ≠ cylinderM1Point k i :=
    disjoint_cylinderCuffs.symm.ne_of_mem hvC (cylinderM1Point_mem_cylinderCuff1 k i)
  apply path_eq_closed_edge_of_forced_first_link (L.isPath i) (L.isSubdrawing i).1
    (fun e he hne => not_mem_closure_edge_of_ne_red3 hval hl hvs he hne) hl
  intro hvU
  have hvbd : v ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inr hvC
  have hx : v ∈ ({cylinderM1Point k i, L.curve i 1} : Set ClosedCylinder) :=
    L.U_inter_boundary hG i ▸ ⟨hvU, hvbd⟩
  rcases hx with hx | hx
  · exact False.elim (hvs hx)
  · exact hx
/-- At a valency-one start with outer-cuff neighbour, the whole linkage
path is incident with the initial region, as used in VI (5.3), page 132. -/
theorem linkage_path_subset_region_closure_of_valency_one {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v) (hvC : v ∈ cylinderCuff2) :
    (L.pathDrawing i).U ⊆ closure (cylinderRegion k G i) := by
  have hvs : v ≠ cylinderM1Point k i :=
    disjoint_cylinderCuffs.symm.ne_of_mem hvC (cylinderM1Point_mem_cylinderCuff1 k i)
  obtain ⟨e, he, w, hws, hle, heR, _⟩ :=
    exists_unique_initial_region_edge L hk hG hθ hno i
  have hscl : cylinderM1Point k i ∈ closure e :=
    (show cylinderM1Point k i ∈ closure e ∩ G.V from hle.2.2.2.symm ▸ mem_insert _ {w}).1
  have hea : e = a := by
    by_contra hne
    exact not_mem_closure_edge_of_ne_red3 hval hl hvs he hne hscl
  rw [(linkage_path_eq_closed_edge_of_valency_one L hG i hval hl hvC).2, ← hea]
  exact closure_minimal heR isClosed_closure
end GraphMinor.GM06
