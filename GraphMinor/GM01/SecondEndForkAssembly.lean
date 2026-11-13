module

public import GraphMinor.GM01.CombTerminalBinaryAttachment
public import GraphMinor.GM01.RootedForkAttachmentPaths
import GraphMinor.GM01.CombTerminalComplement
import GraphMinor.GM01.ConnectedInducedSets
import GraphMinor.GM01.SubdivisionConnected

/-!
# Assembling the fork when both attachments miss the second end

Graph Minors I, (4.12), page 59, contracts the subdivision outside
its second end together with the two attachment paths and the root
path. That union is connected and contains the ambient root. The
second end supplies the binary arm. The final block supplies the
comb arm, reached by the late-region path. The two attachment-path
construction then produces the forbidden rooted fork.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

private theorem path_disjoint_terminal_of_clean_meet {α β : Type*}
    {P D : Graph α β} {E : Set α} {d : α} (hED : E ⊆ V(D))
    (hd : d ∉ E) (hmeet : V(P) ∩ V(D) ⊆ {d}) : Disjoint V(P) E := by
  apply Set.disjoint_left.mpr
  intro x hx hxE
  have hxd : x = d := hmeet ⟨hx, hED hxE⟩
  exact hd (hxd ▸ hxE)

/-- The contraction described in GM01 (4.12), page 59, after the
actual final-block arm and the four paths have been constructed. -/
theorem rootedFork_of_attachments_outside_second_end {α β : Type*} {γ δ L : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 3 ≤ L) (G : RootedGraph α β)
    {D : Graph α β} (hDG : D ≤ G.graph)
    (c : (pathComb (γ - 1) L).verts → α) (hc : Injective c)
    (P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (GP : RootedGraph α β) (hGP : GP.graph ≤ G.graph)
    (MP : RootedMinorModel (rootedPathComb (γ - 1) (δ - 1) (by omega)) GP)
    (hDGP : Disjoint V(D) V(GP.graph))
    {d₁ d₂ w₁ w₂ : α} (hd₁ : d₁ ∈ V(D) \ combSecondEndSupport (by omega) c P)
    (hd₂ : d₂ ∈ V(D) \ combSecondEndSupport (by omega) c P)
    {P₀ P₁ P₂ P₃ : Graph α β}
    (hP₀ : IsGraphPathWithEnds G.graph P₀ G.root.val w₁)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁ w₁)
    (hP₂ : IsGraphPathWithEnds G.graph P₂ d₂ w₂)
    (hP₃ : IsGraphPathWithEnds G.graph P₃ w₂ GP.root.val)
    (hP₀D : V(P₀) ∩ V(D) ⊆ {d₁}) (hP₁D : V(P₁) ∩ V(D) ⊆ {d₁})
    (hP₂D : V(P₂) ∩ V(D) ⊆ {d₂})
    (hP₀GP : Disjoint V(P₀) V(GP.graph)) (hP₁GP : Disjoint V(P₁) V(GP.graph))
    (hP₂GP : Disjoint V(P₂) V(GP.graph))
    (hP₃D : Disjoint V(P₃) V(D)) (hP₃GP : V(P₃) ∩ V(GP.graph) = {GP.root.val}) :
    HasRootedMinor (rootedForkGraph γ δ hγ hδ) G := by
  let E := combSecondEndSupport (by omega : 2 ≤ L) c P
  let GB := rootedCombSegment (by omega : 0 < 2) D c P (L - 2) (by omega : L - 2 + 2 ≤ L)
  obtain ⟨hGBD, ⟨MB⟩, a, ha, Q, hQ, hQmeet⟩ := terminal_binary_arm_attachment hL c hc P hV hPaths hInter
  have hED : E ⊆ V(D) := hGBD.vertexSet_mono
  have hC0connD := comb_terminal_segment_complement_connected (by omega : 0 < L - 2)
    (by omega : 0 < 2) (by omega : L - 2 + 2 = L) c hc P hV hPaths hInter
  let C₀ := V(D) \ E
  have hC₀G : C₀ ⊆ V(G.graph) := sdiff_subset.trans hDG.vertexSet_mono
  have hC₀conn : GraphConnected (G.graph.induce C₀) := graphConnected_induce_of_subgraph
    ((D.induce_le sdiff_subset).trans hDG) hC0connD
  have hP₀E := path_disjoint_terminal_of_clean_meet hED hd₁.2 hP₀D
  have hP₁E := path_disjoint_terminal_of_clean_meet hED hd₁.2 hP₁D
  have hP₂E := path_disjoint_terminal_of_clean_meet hED hd₂.2 hP₂D
  have hC₁conn := graphConnected_induce_union hC₀conn
    (graphConnected_induce_of_subgraph hP₁.le (graphConnected_of_isGraphPath hP₁))
    ⟨d₁, hd₁, hP₁.left_mem⟩
  have hC₂conn := graphConnected_induce_union hC₁conn
    (graphConnected_induce_of_subgraph hP₀.le (graphConnected_of_isGraphPath hP₀))
    ⟨w₁, Or.inr hP₁.right_mem, hP₀.right_mem⟩
  have hCconn := graphConnected_induce_union hC₂conn
    (graphConnected_induce_of_subgraph hP₂.le (graphConnected_of_isGraphPath hP₂))
    ⟨d₂, Or.inl (Or.inl hd₂), hP₂.left_mem⟩
  let C := C₀ ∪ V(P₁) ∪ V(P₀) ∪ V(P₂)
  have hCG : C ⊆ V(G.graph) := union_subset
    (union_subset (union_subset hC₀G hP₁.le.vertexSet_mono) hP₀.le.vertexSet_mono) hP₂.le.vertexSet_mono
  have hC₀E : Disjoint C₀ E := Set.disjoint_left.mpr (fun _ hx hxE ↦ hx.2 hxE)
  have hCE : Disjoint C E := ((hC₀E.union_left hP₁E).union_left hP₀E).union_left hP₂E
  have hCGP : Disjoint C V(GP.graph) :=
    (((hDGP.mono_left sdiff_subset).union_left hP₁GP).union_left hP₀GP).union_left hP₂GP
  exact ⟨rootedForkModelOfAttachmentPaths hγ hδ G C hCG hCconn
    (Or.inl (Or.inr hP₀.left_mem)) hGP (hGBD.trans hDG) MP MB hCGP hCE
    (hDGP.symm.mono_right hGBD.vertexSet_mono)
    (Or.inr hP₂.right_mem) (Or.inl (Or.inl (Or.inl ha))) hP₃ (hQ.mono hDG)
    hP₃GP hQmeet (hP₃D.mono_right hGBD.vertexSet_mono)
    (hDGP.mono_left hQ.le.vertexSet_mono)⟩

end GraphMinor.GM01
