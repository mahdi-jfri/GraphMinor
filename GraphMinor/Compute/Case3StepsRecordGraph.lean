module

public import GraphMinor.Compute.Case3StepsMemberTransport
public import GraphMinor.Compute.Case3StepsScanRecords

/-!
# Identifying the graphs stored in member records

A record maps the consecutively numbered member directly to original
labels. The rural division instead first restores compass labels, then
original labels. The two maps agree on every vertex and directed edge of
the member, so they give the same graph, including isolated vertices.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- Two finite vertex renamings compose on a multigraph even though their
extensions beyond the finite vertex sets need not compose. -/
theorem case3RelabelGraph_orig_comp {k m N : ℕ} (G : MultiDigraph k)
    (f : Fin k → Fin m) (hf : Function.Injective f)
    (g : Fin m → Fin N) (hg : Function.Injective g) :
    relabelGraph (origVertexEmb (g ∘ f) (hg.comp hf))
      (origEdgeEmb (g ∘ f) (hg.comp hf)) G.toGMDigraph.toGraph =
      relabelGraph (origVertexEmb g hg) (origEdgeEmb g hg)
        (relabelGraph (origVertexEmb f hf) (origEdgeEmb f hf) G.toGMDigraph.toGraph) := by
  have hv (u : ℕ) (hu : u < k) :
      origVertexEmb (g ∘ f) (hg.comp hf) u =
        origVertexEmb g hg (origVertexEmb f hf u) := by
    rw [origVertexEmb_apply_val (g ∘ f) (hg.comp hf) ⟨u, hu⟩,
      origVertexEmb_apply_val f hf ⟨u, hu⟩, origVertexEmb_apply_val]
    rfl
  have he (e : ℕ × ℕ × ℕ) (he : e ∈ G.toGMDigraph.toGraph.edgeSet) :
      origEdgeEmb (g ∘ f) (hg.comp hf) e =
        origEdgeEmb g hg (origEdgeEmb f hf e) := by
    rcases e with ⟨u, v, q⟩
    obtain ⟨hu, hv', _⟩ := he
    change (origVertexEmb (g ∘ f) (hg.comp hf) u,
      origVertexEmb (g ∘ f) (hg.comp hf) v, q) =
        (origVertexEmb g hg (origVertexEmb f hf u),
          origVertexEmb g hg (origVertexEmb f hf v), q)
    rw [hv u hu, hv v hv']
  refine Graph.ext ?_ fun e u v => ?_
  · ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨origVertexEmb f hf x, ⟨x, hx, rfl⟩, (hv x hx).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hv x hx⟩
  · constructor
    · rintro ⟨a, x, y, hl, rfl, rfl, rfl⟩
      exact ⟨origEdgeEmb f hf a, origVertexEmb f hf x, origVertexEmb f hf y,
        ⟨a, x, y, hl, rfl, rfl, rfl⟩, (he a hl.edge_mem).symm,
        (hv x hl.left_mem).symm, (hv y hl.right_mem).symm⟩
    · rintro ⟨_, _, _, ⟨a, x, y, hl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
      exact ⟨a, x, y, hl, he a hl.edge_mem, hv x hl.left_mem, hv y hl.right_mem⟩

/-- The graph encoded by a selected record is precisely that selected
member of the full division, restored to original labels. -/
theorem case3SelectedRecord_relabel {n N : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) (Z : Finset (Fin n))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z)
    (e : Fin n ↪ Fin N) :
    let x := case3SimpleSocietyInput D omega homega
    let A := case3SelectedMember x Z i
    let orig := e ∘ A.verts.orderEmbOfFin rfl
    relabelGraph (origVertexEmb orig (e.injective.comp (A.verts.orderEmbOfFin rfl).injective))
      (origEdgeEmb orig (e.injective.comp (A.verts.orderEmbOfFin rfl).injective))
      (case3CompactMember x D Z i).toGMDigraph.toGraph =
        relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
          (case3LiftMember D A (case3AssignedLoops
            (case3OrderedLoopAssignment x Z hdiv) A)) := by
  dsimp only
  rw [case3RelabelGraph_orig_comp _ _
    ((case3SelectedMember (case3SimpleSocietyInput D omega homega) Z i).verts.orderEmbOfFin rfl).injective
    e e.injective, case3CompactMember_relabel D omega homega Z hdiv i]

end GraphMinor.Compute
