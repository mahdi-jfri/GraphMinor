module

public import GraphMinor.GM01.CombSegmentSupports
public import GraphMinor.GM01.RootedSubgraphSubdivisionAttachment
import GraphMinor.GM01.SubdivisionRestriction
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.PathCombTrees

/-!
# Models and connectivity of a selected comb segment

Graph Minors I, (4.10), page 58, retains an initial segment of the old
comb and a final segment of `D`. Their actual supports induce connected
subgraphs and carry rooted models retaining every selected centre.
Restrict the replacing paths to the selected interval, then apply the
proved subdivision contraction and its centre-preservation theorem.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- A selected comb segment rooted at its first selected spine centre.
Its graph is the induced graph on the selected subdivision support. -/
@[expose] def rootedCombSegment {α β : Type*} {γ L m : ℕ} (hm : 0 < m)
    (D : Graph α β) (c : (pathComb γ L).verts → α)
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (offset : ℕ) (hbound : offset + m ≤ L) :
    RootedGraph α β :=
  ⟨D.induce (combSegmentSupport c P offset hbound),
    ⟨c (combShiftEmbedding offset hbound (rootedPathComb γ m hm).root),
      Or.inl (mem_range_self (rootedPathComb γ m hm).root)⟩⟩

/-- A selected comb segment is contained in the represented graph,
is connected, and has a rooted model retaining all selected centres.
These are the two retained pieces in GM01 (4.10), page 58. -/
theorem combSegment_model {α β : Type*} {γ L m : ℕ} (hm : 0 < m)
    {D : Graph α β} (c : (pathComb γ L).verts → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(D)) (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (offset : ℕ) (hbound : offset + m ≤ L) :
    (rootedCombSegment hm D c P offset hbound).graph ≤ D ∧
      GraphConnected (rootedCombSegment hm D c P offset hbound).graph ∧
      ∃ M : RootedMinorModel (rootedPathComb γ m hm) (rootedCombSegment hm D c P offset hbound),
        ∀ w : (pathComb γ m).verts, c (combShiftEmbedding offset hbound w) ∈ M.branch w := by
  classical
  let : Finite (pathComb γ m).verts := (pathComb_vertices_finite γ m).to_subtype
  let f := combShiftEmbedding (γ := γ) offset hbound
  let hf := fun {a b} (h : (pathComb γ m).coe.Adj a b) ↦ combShiftEmbedding_adj offset hbound h
  let A := combSegmentSupport c P offset hbound
  let paths := fun e : (pathComb γ m).coe.edgeSet ↦ P (subdivisionEmbeddingEdges f hf e)
  have hPathD : ∀ e, V(paths e) ⊆ A := by
    intro e x hx
    exact Or.inr (Set.mem_iUnion.mpr ⟨e, hx⟩)
  have hA : A ⊆ V(D) := by
    intro x hx
    rcases hx with ⟨v, rfl⟩ | hxP
    · exact hcentres (f v)
    · obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hxP
      obtain ⟨_, _, _, hP, _⟩ := hPaths (subdivisionEmbeddingEdges f hf e)
      exact hP.le.vertexSet_mono hxe
  have hselected := subdivision_restriction_paths f hf c A P hPaths hInter hPathD
  have hCS : ∀ v, c (f v) ∈ V(D.induce A) := fun v ↦ Or.inl (mem_range_self v)
  let root := (rootedPathComb γ m hm).root
  have hconn : GraphConnected (D.induce A) := by
    apply subdivision_connected (pathComb_connected (γ := γ) hm).coe root
      (D.induce A) (fun v ↦ c (f v)) paths rfl
    intro e
    obtain ⟨a, b, he, hP, _⟩ := hselected.1 e
    have hab : (pathComb γ m).coe.Adj a b := by
      have h := e.property
      rw [he] at h
      exact h
    exact ⟨a, b, he, hab, hP⟩
  let x : V(D.induce A) := ⟨c (f root), hCS root⟩
  let M := rootedSubgraphSubdivisionAtVertex (pathComb γ m) (fun v ↦ c (f v))
    (hc.comp f.injective) hCS paths hselected.1 (fun e e' hne ↦ (hselected.2 e e' hne).1)
    root x (Or.inl rfl)
  refine ⟨D.induce_le hA, hconn, M, ?_⟩
  intro w
  exact rootedSubgraphSubdivisionAtVertex_centre_mem (pathComb γ m) (fun v ↦ c (f v))
    (hc.comp f.injective) hCS paths hselected.1 (fun e e' hne ↦ (hselected.2 e e' hne).1)
    root x (Or.inl rfl) w

end GraphMinor.GM01
