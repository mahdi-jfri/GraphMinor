module

public import GraphMinor.GM02.SideBoundaryPath

/-!
# Distinct pieces have distinct endpoint pairs

The contracted path of an original pair is simple, so its edges do not
repeat. Its edge list is the ordered list of side-piece pairs. Pieces from
different original pairs have disjoint vertices. Thus every piece is
uniquely determined by its endpoint pair, even across the two colors.
In particular the two extracted terminations have disjoint pair sets,
which is needed to verify the parity condition in corrected II (2.9).
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph List Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

include hP in
/-- Across both colors, the endpoint pair identifies its maximal path piece. -/
theorem RunPieceIndex.pair_injective : Function.Injective (RunPieceIndex.pair A G H P) := by
  intro i j heq
  have hpq : i.1 = j.1 := by
    by_contra hn
    let a := (i.pair A G H P).out.1
    have haI : a ∈ (i.path A G H P).vertices :=
      (i.path A G H P).endpoint_mem (Sym2.out_fst_mem _)
    have haJ : a ∈ (j.path A G H P).vertices :=
      (j.path A G H P).endpoint_mem (heq ▸ Sym2.out_fst_mem _)
    exact Set.disjoint_left.1 (hP i.1 j.1 hn) (i.vertices_subset A G H P haI)
      (j.vertices_subset A G H P haJ)
  rcases i with ⟨p, r⟩
  rcases j with ⟨q, s⟩
  change p = q at hpq
  subst q
  have hnd := (sideBoundaryPairPath A G H P hP p).isPath.isTrail.edges_nodup
  rw [sideBoundaryPairPath_edges_records] at hnd
  have hEq :
      s((dartFullRecord (separationEdgeColor H) (P p).start r.val).2.headD (P p).start,
        (dartFullRecord (separationEdgeColor H) (P p).start r.val).2.getLastD (P p).start) =
      s((dartFullRecord (separationEdgeColor H) (P p).start s.val).2.headD (P p).start,
        (dartFullRecord (separationEdgeColor H) (P p).start s.val).2.getLastD (P p).start) :=
    (RunPieceIndex.pair_eq_fullRecord A G H P ⟨p, r⟩).symm.trans
      (heq.trans (RunPieceIndex.pair_eq_fullRecord A G H P ⟨p, s⟩))
  have hrs : r.val = s.val := List.inj_on_of_nodup_map hnd r.property s.property hEq
  exact congrArg (fun t => (⟨p, t⟩ : RunPieceIndex A G H P)) (Subtype.ext hrs)

/-- The two extracted termination matchings share no pair edge. -/
theorem sideTermination_pairs_disjoint :
    Disjoint ((sideTermination A G H P hP true).pairs : Set (Sym2 α))
      ((sideTermination A G H P hP false).pairs : Set (Sym2 α)) := by
  apply Set.disjoint_left.2
  intro e heL heR
  obtain ⟨i, hiC, hi⟩ := (mem_sideTermination_pairs A G H P hP true e).1 heL
  obtain ⟨j, hjC, hj⟩ := (mem_sideTermination_pairs A G H P hP false e).1 heR
  have hij := RunPieceIndex.pair_injective A G H P hP (hi.trans hj.symm)
  rw [hij, hjC] at hiC
  contradiction

end GraphMinor.GM02
