module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPathTube
import GraphMinor.LRPlanarity.TreeNeighborhoodGluing
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundary

/-!
# A path tube is a disc with two endpoint attachment intervals

Part IV, Section 7b of the planarity note glues strips and bend polygons
one at a time. The same two disc gluings used for a tree leaf join a new
strip to the preceding tube through its bend polygon. A simple path ensures
that the new strip misses the old tube. The two original endpoint intervals
remain on the boundary, ready for the original tree's leaf induction.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface SimpleGraph

/-- Part IV, Section 7b: a nonempty simple subdivision path has a disc tube,
meeting its two endpoint polygons in boundary lines. All hypotheses describe
the individual polygons, strips and their exact local intersections. -/
theorem walkTube_isClosedDisc {V : Type*} {G : SimpleGraph V}
    (P : V → Set ℂ) (R L : V → V → Set ℂ)
    (hP : ∀ u, IsClosedDisc (P u))
    (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (hR : ∀ u v, G.Adj u v → IsClosedDisc (R u v))
    (hline : ∀ u v, G.Adj u v → ∃ a b, IsLineWithEnds (L u v) a b)
    (hinter : ∀ u v, G.Adj u v → R u v ∩ P u = L u v ∧ R u v ∩ P v = L v u)
    (hbd : ∀ u v, G.Adj u v → L u v ⊆ discBd (P u) ∧
      L u v ⊆ discBd (R u v) ∧ L v u ⊆ discBd (R u v))
    (hRsep : ∀ u v, G.Adj u v → ∀ z t, G.Adj z t →
      s(u,v) ≠ s(z,t) → Disjoint (R u v) (R z t))
    (haway : ∀ u v, G.Adj u v → ∀ z, z ≠ u → z ≠ v → Disjoint (R u v) (P z))
    {u t : V} (w : G.Walk u t) (hw : w.IsPath) (hnil : ¬ w.Nil) :
    IsClosedDisc (walkTube P R w) ∧
      ∃ a b c d, IsLineWithEnds (P u ∩ walkTube P R w) a b ∧
        IsLineWithEnds (walkTube P R w ∩ P t) c d ∧
        P u ∩ walkTube P R w ⊆ discBd (P u) ∧
        P u ∩ walkTube P R w ⊆ discBd (walkTube P R w) ∧
        walkTube P R w ∩ P t ⊆ discBd (walkTube P R w) ∧
        walkTube P R w ∩ P t ⊆ discBd (P t) := by
  induction w with
  | nil => exact (hnil Walk.Nil.nil).elim
  | @cons u v t huv q ih =>
    cases q with
    | nil =>
      rw [walkTube_single]
      obtain ⟨a, b, hab⟩ := hline u v huv
      obtain ⟨c, d, hcd⟩ := hline v u huv.symm
      rw [inter_comm (P u), (hinter u v huv).1, (hinter u v huv).2]
      exact ⟨hR u v huv, a, b, c, d, hab, hcd, (hbd u v huv).1,
        (hbd u v huv).2.1, (hbd u v huv).2.2, (hbd v u huv.symm).1⟩
    | @cons v z t hvz tail =>
      let q := Walk.cons hvz tail
      have hq : q.IsPath := hw.of_cons
      have hu : u ∉ q.support := (Walk.cons_isPath_iff huv q).mp hw |>.2
      have hvt : v ≠ t := fun he => Walk.not_nil_cons (hq.nil_iff_eq.mpr he)
      have htu : t ≠ u := fun he => hu (he ▸ q.end_mem_support)
      obtain ⟨hQ, a, b, c, d, hstart, hend, hstartP, hstartQ, hendQ, hendP⟩ :=
        ih hq Walk.not_nil_cons
      obtain ⟨e, f, hnewline⟩ := hline v u huv.symm
      have hnewmeet : P v ∩ R u v = L v u := by
        rw [inter_comm]
        exact (hinter u v huv).2
      have hQmeet : walkTube P R q ∩ P v = P v ∩ walkTube P R q := inter_comm _ _
      have hQR := walkTube_disjoint_preceding_strip P R hRsep haway huv q hq hu
      have hQPu := walkTube_disjoint_polygon P R hPsep haway q hu
      have hRPt := haway u v huv t htu hvt.symm
      have hPvPt := hPsep hvt
      have hglue := attach_tree_leaf_discs hQ (hP v) (hR u v huv) hstart hnewline
        hQmeet hnewmeet hQR hstartQ hstartP (hbd v u huv.symm).1 (hbd u v huv).2.2
      have hU : walkTube P R (Walk.cons huv q) = walkTube P R q ∪ P v ∪ R u v := by
        rw [walkTube_cons_cons]
        ac_rfl
      rw [hU]
      have hfirst : P u ∩ (walkTube P R q ∪ P v ∪ R u v) = L u v := by
        rw [inter_comm, union_inter_distrib_right, union_inter_distrib_right,
          hQPu.inter_eq, (hPsep huv.ne.symm).inter_eq, empty_union,
          empty_union, (hinter u v huv).1]
      have hlast : (walkTube P R q ∪ P v ∪ R u v) ∩ P t = walkTube P R q ∩ P t := by
        rw [union_inter_distrib_right, union_inter_distrib_right,
          hPvPt.inter_eq, hRPt.inter_eq, union_empty, union_empty]
      have hLsubP : L u v ⊆ P u := fun x hx => ((hinter u v huv).1.symm ▸ hx).2
      have hKsubP : L v u ⊆ P v := fun x hx => ((hinter u v huv).2.symm ▸ hx).2
      have hLK : Disjoint (L u v) (L v u) := (hPsep huv.ne).mono hLsubP hKsubP
      have hfirstBd := new_boundary_survives_leaf_attachment hQ (hP v) (hR u v huv)
        hstart hnewline hQmeet hnewmeet hQR hstartQ hstartP
        (hbd v u huv.symm).1 (hbd u v huv).2.2 (hbd u v huv).2.1 hLK
      have hlastL : Disjoint (walkTube P R q ∩ P t) (P v ∩ walkTube P R q) :=
        hPvPt.symm.mono inter_subset_right inter_subset_left
      have hlastK : Disjoint (walkTube P R q ∩ P t) (L v u) :=
        hPvPt.symm.mono inter_subset_right hKsubP
      have hlastBd := old_boundary_survives_leaf_attachment hQ (hP v) (hR u v huv)
        hstart hnewline hQmeet hnewmeet hQR hstartQ hstartP
        (hbd v u huv.symm).1 (hbd u v huv).2.2 hendQ hlastL hlastK
      obtain ⟨a', b', hab'⟩ := hline u v huv
      rw [hfirst, hlast]
      exact ⟨hglue.1, a', b', c, d, hab', hend, (hbd u v huv).1,
        hfirstBd, hlastBd, hendP⟩

end GraphMinor.LRPlanarity
