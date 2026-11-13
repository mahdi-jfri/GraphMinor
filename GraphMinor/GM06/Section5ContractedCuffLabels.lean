module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5ProperPaths
import GraphMinor.GM06.Section5Red

/-!
# Cuff labels after contracting an initial edge

Reduction 3 in VI (5.7), page 133, retains the cuff labels while
retiring the neighbour of an initial vertex. That neighbour is an
interior vertex: the linkage path meets the boundary only at its
two ends, and Reduction 3 excludes its outer end. A boundary-fixing
collapse cannot send another vertex to the boundary, since it is
injective outside the chosen closed edge. On that edge the only
vertices are its two ends. Removing the interior neighbour therefore
leaves exactly the same labelled cuff points and the same cuff rows.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The neighbour retired by Reduction 3 lies off both cuffs. -/
theorem CylinderLinkage.initial_neighbour_not_mem_boundary
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (he : e ∈ (L.pathDrawing i).E)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hoff : v ∉ cylinderCuff2) :
    v ∉ bd ClosedCylinder := by
  have hlP := ((L.isSubdrawing i).1.isLink_iff he).mpr hl
  have hvU := (L.pathDrawing i).V_subset_U hlP.right_mem
  intro hvbd
  have hvends : v ∈ ({cylinderM1Point k i, L.curve i 1} : Set ClosedCylinder) :=
    L.U_inter_boundary hG i ▸ ⟨hvU, hvbd⟩
  rcases hvends with hs | ht
  · exact hvs hs
  · obtain ⟨j, hj⟩ := L.curve_one_mem i
    exact hoff ((mem_singleton_iff.mp ht).symm ▸ hj ▸ cylinderM2Point_mem_cylinderCuff2 k j)

/-- A collapse fixing the boundary has no new boundary preimages
outside its collapsed fiber. -/
theorem eq_of_initial_edge_collapse_mem_boundary
    {k : ℕ} {i : Fin k} {e : Set ClosedCylinder}
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure e)
    (hi : InjOn π (closure e)ᶜ)
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    {x : ClosedCylinder} (hx : π x ∈ bd ClosedCylinder)
    (hxs : π x ≠ cylinderM1Point k i) : π x = x := by
  have hπcl : ∀ y ∈ closure e, π y = cylinderM1Point k i := by
    intro y hy
    have hy' : y ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hy
    exact hy'
  have hxnot : x ∉ closure e := fun hy => hxs (hπcl x hy)
  have hynot : π x ∉ closure e := by
    intro hy
    exact hxs ((hbd (π x) hx).symm.trans (hπcl (π x) hy))
  exact (hi hxnot hynot (hbd (π x) hx).symm).symm

/-- On surviving labels, membership in any chosen subset of the
boundary is preserved by the actual collapse. In particular both
cuff arrays can be retained without changing their words. -/
theorem contracted_boundary_label_iff
    {n k : ℕ} {G : Drawing ClosedCylinder} {i : Fin k}
    (vertex : Fin n ↪ ClosedCylinder) (vertex' : Fin n → ClosedCylinder)
    (A : Finset (Fin n)) (b : Fin n)
    (hvertex : ∀ x ∈ A, vertex x ∈ G.V)
    {e : Set ClosedCylinder}
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) (vertex b))
    (hb : vertex b ∉ bd ClosedCylinder)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure e)
    (hi : InjOn π (closure e)ᶜ)
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    (hv : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
    (S : Set ClosedCylinder) (hS : S ⊆ bd ClosedCylinder) (x : Fin n) :
    (x ∈ A.erase b ∧ vertex' x ∈ S) ↔ (x ∈ A ∧ vertex x ∈ S) := by
  classical
  constructor
  · rintro ⟨hx, hxS⟩
    have hxA := (Finset.mem_erase.mp hx).2
    have hxb := (Finset.mem_erase.mp hx).1
    have hπS : π (vertex x) ∈ S := hv x hx ▸ hxS
    have hfix : π (vertex x) = vertex x := by
      by_cases hxs : π (vertex x) = cylinderM1Point k i
      · have hxcl : vertex x ∈ closure e := by
          rw [← hfiber]
          exact hxs
        have hxends : vertex x ∈ ({cylinderM1Point k i, vertex b} : Set ClosedCylinder) :=
          hl.2.2.2 ▸ ⟨hxcl, hvertex x hxA⟩
        rcases hxends with ha | hb'
        · exact hxs.trans ha.symm
        · exact False.elim (hxb (vertex.injective (mem_singleton_iff.mp hb')))
      · exact eq_of_initial_edge_collapse_mem_boundary π hfiber hi hbd (hS hπS) hxs
    exact ⟨hxA, hfix ▸ hπS⟩
  · rintro ⟨hxA, hxS⟩
    have hxb : x ≠ b := by
      intro h
      exact hb (h ▸ hS hxS)
    have hx : x ∈ A.erase b := Finset.mem_erase.mpr ⟨hxb, hxA⟩
    refine ⟨hx, ?_⟩
    rw [hv x hx, hbd (vertex x) (hS hxS)]
    exact hxS

/-- Every old cuff label remains live, at exactly its old point. -/
theorem contracted_label_eq_on_boundary
    {n : ℕ} (vertex : Fin n → ClosedCylinder) (vertex' : Fin n → ClosedCylinder)
    (A : Finset (Fin n)) (b : Fin n) (hb : vertex b ∉ bd ClosedCylinder)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    (hv : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
    {x : Fin n} (hx : x ∈ A) (hxb : vertex x ∈ bd ClosedCylinder) :
    x ∈ A.erase b ∧ vertex' x = vertex x := by
  classical
  have hne : x ≠ b := by intro h; exact hb (h ▸ hxb)
  have hlive := Finset.mem_erase.mpr ⟨hne, hx⟩
  exact ⟨hlive, (hv x hlive).trans (hbd (vertex x) hxb)⟩

/-- The numeric cuff row still enumerates exactly the labelled cuff
vertices after the contraction, for either component of the boundary. -/
theorem contracted_cuff_row_iff
    {n k : ℕ} {G : Drawing ClosedCylinder} {i : Fin k}
    (vertex : Fin n ↪ ClosedCylinder) (vertex' : Fin n → ClosedCylinder)
    (A : Finset (Fin n)) (b : Fin n)
    (hvertex : ∀ x ∈ A, vertex x ∈ G.V)
    {e : Set ClosedCylinder}
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) (vertex b))
    (hb : vertex b ∉ bd ClosedCylinder)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure e)
    (hi : InjOn π (closure e)ᶜ)
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    (hv : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
    (S : Set ClosedCylinder) (hS : S ⊆ bd ClosedCylinder)
    (row : List ℕ) (hrow : ∀ x : Fin n, x.val ∈ row ↔ x ∈ A ∧ vertex x ∈ S) :
    ∀ x : Fin n, x.val ∈ row ↔ x ∈ A.erase b ∧ vertex' x ∈ S := by
  intro x
  exact (hrow x).trans
    (contracted_boundary_label_iff vertex vertex' A b hvertex hl hb π hfiber hi hbd hv S hS x).symm

end GraphMinor.GM06
