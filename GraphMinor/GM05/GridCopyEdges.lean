module

public import GraphMinor.GM05.GridCopyVertices
public import GraphMinor.GM05.GraphCopies

/-!
# Edge maps for disjoint grid copies

Map each grid edge by the vertex placement of its copy. Distinct edge
labels remain distinct because the vertex placement is injective on all
copy vertices. Incidence with a placed vertex is exactly incidence in the
original copy graph. Grid edges have distinct ends, so none becomes a loop.
-/

public section

namespace GraphMinor.GM05

open Graph SimpleGraph Set GM01

/-- Place an edge in the same row block as the vertices of its copy. -/
@[expose] def gridCopyEdge {k θ : ℕ} (e : Fin k × Sym2 (Fin θ × Fin θ)) :
    Sym2 (Fin ((k+1)*θ) × Fin ((k+1)*θ)) :=
  Sym2.map (fun w ↦ gridCopyVertex (e.1,w)) e.2

/-- Edge placement is injective, including on unused labels. -/
theorem gridCopyEdge_injective {k θ : ℕ} : Function.Injective (@gridCopyEdge k θ) := by
  rintro ⟨i,e⟩ ⟨j,f⟩ he
  induction e with
  | h u v =>
    induction f with
    | h x y =>
      change s(gridCopyVertex (i,u),gridCopyVertex (i,v))=
        s(gridCopyVertex (j,x),gridCopyVertex (j,y)) at he
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
      · have hp := gridCopyVertex_injective h1
        have hq := gridCopyVertex_injective h2
        exact Prod.ext (congrArg (fun p : Fin k × (Fin θ × Fin θ) ↦ p.1) hp)
          (congrArg₂ (fun a b ↦ s(a,b)) (congrArg (fun p : Fin k × (Fin θ × Fin θ) ↦ p.2) hp) (congrArg (fun p : Fin k × (Fin θ × Fin θ) ↦ p.2) hq))
      · have hp := gridCopyVertex_injective h1
        have hq := gridCopyVertex_injective h2
        exact Prod.ext (congrArg (fun p : Fin k × (Fin θ × Fin θ) ↦ p.1) hp)
          ((congrArg₂ (fun a b ↦ s(a,b)) (congrArg (fun p : Fin k × (Fin θ × Fin θ) ↦ p.2) hp) (congrArg (fun p : Fin k × (Fin θ × Fin θ) ↦ p.2) hq)).trans Sym2.eq_swap)

/-- Incidence of a valid placed edge at a placed vertex is exactly the
incidence in the graph of disjoint grid copies. -/
theorem gridCopyEdge_inc {k θ : ℕ} {e : Fin k × Sym2 (Fin θ × Fin θ)}
    (he : e∈E(graphCopies k (gridGraph θ))) (p : Fin k × (Fin θ × Fin θ)) :
    (gridGraph ((k+1)*θ)).Inc (gridCopyEdge e) (gridCopyVertex p) ↔
      (graphCopies k (gridGraph θ)).Inc e p := by
  obtain ⟨u,v,hl⟩ := exists_isLink_of_mem_edgeSet he.2
  have hcopy : (graphCopies k (gridGraph θ)).IsLink e (e.1,u) (e.1,v) := ⟨rfl,rfl,hl⟩
  have hbig := gridCopyVertex_link e.1 hl
  constructor
  · intro hp
    rcases hp.eq_or_eq_of_isLink hbig with h|h
    · have hp := gridCopyVertex_injective h
      subst p
      exact hcopy.inc_left
    · have hp := gridCopyVertex_injective h
      subst p
      exact hcopy.inc_right
  · intro hp
    rcases hp.eq_or_eq_of_isLink hcopy with rfl|rfl
    · exact hbig.inc_left
    · exact hbig.inc_right

/-- A source grid edge has two distinct placed ends, so neither a source
loop nor a branch containing all its ends is possible in a singleton model. -/
theorem gridCopyEdge_loop_iff {k θ : ℕ} {e : Fin k × Sym2 (Fin θ × Fin θ)}
    (he : e∈E(graphCopies k (gridGraph θ))) (p : Fin k × (Fin θ × Fin θ)) :
    (graphCopies k (gridGraph θ)).IsLoopAt e p ↔
      ∀ x, (gridGraph ((k+1)*θ)).Inc (gridCopyEdge e) x → x=gridCopyVertex p := by
  obtain ⟨u,v,hl⟩ := exists_isLink_of_mem_edgeSet he.2
  have huv : u≠v := by
    have heAdj : s(u,v)∈(pathGraph θ □ pathGraph θ).edgeSet := hl.1 ▸ hl.2
    have hadj : (pathGraph θ □ pathGraph θ).Adj u v := heAdj
    exact hadj.ne
  have hcopy : (graphCopies k (gridGraph θ)).IsLink e (e.1,u) (e.1,v) := ⟨rfl,rfl,hl⟩
  have hbig := gridCopyVertex_link e.1 hl
  constructor
  · intro hloop
    have hp : (e.1,u)=p := (hcopy.left_eq_or_eq hloop).elim id id
    have hq : (e.1,v)=p := (hcopy.right_eq_or_eq hloop).elim id id
    exact (huv (congrArg Prod.snd (hp.trans hq.symm))).elim
  · intro hall
    have hp := hall _ hbig.inc_left
    have hq := hall _ hbig.inc_right
    have heq := gridCopyVertex_injective (hp.trans hq.symm)
    exact (huv (congrArg Prod.snd heq)).elim

end GraphMinor.GM05
