module

public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.RootedGraphs

/-!
# Branch sets for joining the two arms of the rooted fork

The contraction in Graph Minors I, (4.1), page 55, joins the retained
path comb and the skipped binary tree to a connected root piece. Use
that piece for the new root branch and the existing model branches for
the two arms. Their supporting graphs are disjoint, so the full family
is disjoint. Their connectivity persists in the ambient graph.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph

/-- The root piece and the two arm models, indexed by the actual vertices
of `Q(γ,δ)`. These are data for the contraction in GM01 (4.1). -/
def rootedForkBranch {α β : Type*} {γ δ : ℕ} (hδ : 2 ≤ δ) (C : Set α)
    {GP GB : RootedGraph α β}
    (MP : RootedMinorModel (rootedPathComb (γ - 1) (δ - 1) (by omega)) GP)
    (MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB) :
    (rootedFork γ δ hδ).verts → Set α
  | ⟨none, _⟩ => C
  | ⟨some (.inl p), hp⟩ => MP.branch ⟨p, hp⟩
  | ⟨some (.inr word), hw⟩ => MB.branch ⟨word, hw⟩

/-- Disjoint supporting graphs keep all fork branches disjoint. -/
theorem rootedForkBranch_pairwise_disjoint {α β : Type*} {γ δ : ℕ} (hδ : 2 ≤ δ)
    (C : Set α) {GP GB : RootedGraph α β}
    (MP : RootedMinorModel (rootedPathComb (γ - 1) (δ - 1) (by omega)) GP)
    (MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB)
    (hCP : Disjoint C V(GP.graph)) (hCB : Disjoint C V(GB.graph))
    (hPB : Disjoint V(GP.graph) V(GB.graph)) :
    Pairwise fun v w ↦ Disjoint (rootedForkBranch hδ C MP MB v) (rootedForkBranch hδ C MP MB w) := by
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  cases v with
  | none =>
    cases w with
    | none => exact hne (Subtype.ext rfl)
    | some w =>
      cases w with
      | inl p => exact Set.disjoint_left.mp hCP hx (MP.branch_subset ⟨p, hw⟩ hy)
      | inr word => exact Set.disjoint_left.mp hCB hx (MB.branch_subset ⟨word, hw⟩ hy)
  | some v =>
    cases v with
    | inl p =>
      cases w with
      | none => exact Set.disjoint_left.mp hCP hy (MP.branch_subset ⟨p, hv⟩ hx)
      | some w =>
        cases w with
        | inl q =>
          have hpq : (⟨p, hv⟩ : (pathComb (γ - 1) (δ - 1)).verts) ≠ ⟨q, hw⟩ := by
            intro heq
            exact hne (Subtype.ext (congrArg (fun z ↦ some (Sum.inl z.val)) heq))
          exact Set.disjoint_left.mp (MP.branch_disjoint hpq) hx hy
        | inr word =>
          exact Set.disjoint_left.mp hPB (MP.branch_subset ⟨p, hv⟩ hx)
            (MB.branch_subset ⟨word, hw⟩ hy)
    | inr word =>
      cases w with
      | none => exact Set.disjoint_left.mp hCB hy (MB.branch_subset ⟨word, hv⟩ hx)
      | some w =>
        cases w with
        | inl p =>
          exact Set.disjoint_left.mp hPB (MP.branch_subset ⟨p, hw⟩ hy)
            (MB.branch_subset ⟨word, hv⟩ hx)
        | inr word' =>
          have hww : (⟨word, hv⟩ : (binaryTree (γ - 1)).verts) ≠ ⟨word', hw⟩ := by
            intro heq
            exact hne (Subtype.ext (congrArg (fun z ↦ some (Sum.inr z.val)) heq))
          exact Set.disjoint_left.mp (MB.branch_disjoint hww) hx hy

/-- Each arm branch stays connected when included in the ambient graph;
the new root branch uses the connected root piece. -/
theorem rootedForkBranch_connected {α β : Type*} {γ δ : ℕ} (hδ : 2 ≤ δ)
    {G : Graph α β} (C : Set α) (hC : GraphConnected (G.induce C))
    {GP GB : RootedGraph α β} (hGP : GP.graph ≤ G) (hGB : GB.graph ≤ G)
    (MP : RootedMinorModel (rootedPathComb (γ - 1) (δ - 1) (by omega)) GP)
    (MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB)
    (v : (rootedFork γ δ hδ).verts) :
    GraphConnected (G.induce (rootedForkBranch hδ C MP MB v)) := by
  let GP' : RootedGraph α β := ⟨G, ⟨GP.root.val, hGP.vertexSet_mono GP.root.property⟩⟩
  let GB' : RootedGraph α β := ⟨G, ⟨GB.root.val, hGB.vertexSet_mono GB.root.property⟩⟩
  let MP' := MP.mono (G' := GP') hGP rfl
  let MB' := MB.mono (G' := GB') hGB rfl
  obtain ⟨v, hv⟩ := v
  cases v with
  | none => exact hC
  | some v =>
    cases v with
    | inl p => exact MP'.branch_connected ⟨p, hv⟩
    | inr word => exact MB'.branch_connected ⟨word, hv⟩

end GraphMinor.GM01
