module

public import GraphMinor.Compute.Case3StepsCoreGroupingProg

/-!
# Keeping ordered compass data abstract after step (5)

The grouping program already computes the compact compass and its society
input. Return the vertex set, multigraph, and corner list as separate data,
with equalities to their computed values. Later RAM proofs can then use
these data without expanding the compass definition during execution.
-/

public section

namespace GraphMinor.Compute

/-- The grouping computation returns its ordered compact graph and corner
list explicitly, with the same uniform time and frame bounds. -/
theorem case3CoreGroupingProg_ordered_exec (h : ℕ) (h2 : 2 ≤ h) (he : Even h) (shiloachProg : Cmd)
    (h86 : ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg86Output x (decAlg86Out x out))
      (alg86Prog shiloachProg) (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (a_G a_VK a_W a_base r_base : ℕ),
        a_G < a_base → a_VK < a_base → a_W < a_base →
        ∀ (w n : ℕ) (G : MultiDigraph n) (X : Finset (Fin n))
          (W : WallOfHeight h (G.deleteVertices X)) (hW : W.IsValid),
          W.IsFlatWall h2 → Disjoint W.compassFinset X →
          wordSize c ((n + 1) * (G.numEdges + n + 1)) ≤ w →
          ∀ s : State, s.arrs a_G = G.enc → s.arrs a_VK = bitSetList W.compassFinset →
            s.arrs a_W = W.encList →
            ∃ S : Finset (Fin n), S = W.compassFinset ∧
            ∃ D : MultiDigraph S.card,
              HEq D (case3CompactCompassMultigraph (G.deleteVertices X) W) ∧
            ∃ (om : List (Fin S.card)) (hom : om.Nodup),
              HEq om (List.ofFn (compactCorner W h2 he)) ∧
            let x := case3SimpleSocietyInput D om hom
            ∃ (s' : State) (t : ℕ)
              (d : Alg86DivisionOutput x),
              Exec w (case3CoreGroupingProg h2 shiloachProg a_G a_VK a_W a_base r_base) s s' t ∧
              t ≤ C * (n + 1) * (G.numEdges + n + 1) ∧
              IsValidAlg86DivisionOutput x d ∧
              (∀ a ∈ case3RoutingArrayIndices,
                s'.arrs (a_base + a) = case3RoutingArray x D d.core.Z a) ∧
              s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1) ∧
              (∀ r ∈ case3RoutingRegIndices, s'.regs (r_base + r) = case3RoutingReg x D r) ∧
              (∀ a < a_base, s'.arrs a = s.arrs a) ∧ (∀ r < r_base, s'.regs r = s.regs r) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := case3CoreGroupingProg_exec h h2 he shiloachProg h86
  refine ⟨C, c, hC, hc, ?_⟩
  intro a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj hw s hin hVK hWall
  obtain ⟨x, hx, D, hD, s', t, d, hex, ht, hd, hroutes, hrank, hregs, harr, hreg⟩ :=
    hrun a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj hw s hin hVK hWall
  subst x
  cases hD
  refine ⟨W.compassFinset, rfl, case3CompactCompassMultigraph (G.deleteVertices X) W,
    HEq.rfl, List.ofFn (compactCorner W h2 he),
    List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW), HEq.rfl,
    s', t, d, hex, ht, hd, hroutes, hrank, hregs, harr, hreg⟩

end GraphMinor.Compute
