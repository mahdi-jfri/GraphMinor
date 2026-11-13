module

public import GraphMinor.GM02.Feasibility
public import GraphMinor.GM02.TerminationMaps

/-!
# Transporting feasible terminated graphs through vertex names

A graph embedding maps every prescribed path to a path and preserves
vertex disjointness. Renaming the pairs by the same embedding therefore
preserves feasibility. Changing just the stated containing vertex set
leaves feasibility unchanged. These operations support compact numbering
of induced recursive instances in II (3.2).
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u u' v v'

/-- Map a pair path along an injective graph homomorphism. -/
noncomputable def PairPath.mapHom {α : Type u} {α' : Type u'} {F : SimpleGraph α}
    {F' : SimpleGraph α'} {p : Sym2 α} (P : PairPath F p) (φ : F →g F')
    (hφ : Function.Injective φ) : PairPath F' (p.map φ) where
  start := φ P.start
  finish := φ P.finish
  ends_eq := congrArg (Sym2.map φ) P.ends_eq
  walk := P.walk.map φ
  isPath := P.isPath.map hφ

/-- Path transport maps exactly its vertex support. -/
theorem PairPath.mapHom_vertices {α : Type u} {α' : Type u'} {F : SimpleGraph α}
    {F' : SimpleGraph α'} {p : Sym2 α} (P : PairPath F p) (φ : F →g F')
    (hφ : Function.Injective φ) : (P.mapHom φ hφ).vertices = φ '' P.vertices := by
  ext a
  simp only [PairPath.mapHom, PairPath.vertices, Walk.support_map, List.mem_map, Set.mem_image,
    Set.mem_ofPred_eq]

/-- The prescribed pair set alone determines feasibility, independently of
which containing vertex set is used to type the termination. -/
theorem feasible_iff_of_pairs_eq {α : Type u} {β : Type v} {S T : Set α}
    (A : Termination S) (B : Termination T) (G : Graph α β) (h : A.pairs = B.pairs) :
    A.Feasible G ↔ B.Feasible G := by
  unfold Termination.Feasible
  rw [h]

/-- Replacing the containing vertex set preserves the same path problem. -/
theorem Termination.feasible_rebase_iff {α : Type u} {β : Type v} {S T : Set α}
    (A : Termination S) (h : A.support ⊆ T) (G : Graph α β) :
    (A.rebase h).Feasible G ↔ A.Feasible G := Iff.rfl

/-- Mapping a feasible family along an injective graph homomorphism
preserves feasibility of its renamed termination. -/
theorem Termination.Feasible.mapHom {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
    {S : Set α} {A : Termination S} {G : Graph α β} {H : Graph α' β'}
    (hA : A.Feasible G) (φ : pathGraph G →g pathGraph H) (hφ : Function.Injective φ) :
    (A.mapEmbedding ⟨φ, hφ⟩).Feasible H := by
  obtain ⟨P, hP⟩ := hA
  let B := A.mapEmbedding ⟨φ, hφ⟩
  have hpreExists (p : {p // p ∈ B.pairs}) : ∃ q ∈ A.pairs, q.map φ = p.val :=
    Finset.mem_image.1 p.property
  let pre (p : {p // p ∈ B.pairs}) : {q // q ∈ A.pairs} :=
    ⟨(hpreExists p).choose, (hpreExists p).choose_spec.1⟩
  have hpre (p : {p // p ∈ B.pairs}) : (pre p).val.map φ = p.val :=
    (hpreExists p).choose_spec.2
  let Q : ∀ p : {p // p ∈ B.pairs}, PairPath (pathGraph H) p.val := fun p =>
    { start := φ (P (pre p)).start
      finish := φ (P (pre p)).finish
      ends_eq := ((P (pre p)).mapHom φ hφ).ends_eq.trans (hpre p)
      walk := ((P (pre p)).mapHom φ hφ).walk
      isPath := ((P (pre p)).mapHom φ hφ).isPath }
  refine ⟨Q, ?_⟩
  intro p q hpq
  have hne : pre p ≠ pre q := by
    intro h
    apply hpq
    apply Subtype.ext
    exact (hpre p).symm.trans ((congrArg (fun r : {r // r ∈ A.pairs} => r.val.map φ) h).trans (hpre q))
  change Disjoint ((P (pre p)).mapHom φ hφ).vertices ((P (pre q)).mapHom φ hφ).vertices
  rw [PairPath.mapHom_vertices, PairPath.mapHom_vertices]
  apply Set.disjoint_left.2
  intro a hap haq
  obtain ⟨b, hb, rfl⟩ := hap
  obtain ⟨c, hc, hcb⟩ := haq
  have he : c = b := hφ hcb
  exact Set.disjoint_left.1 (hP (pre p) (pre q) hne) hb (he ▸ hc)

/-- A graph isomorphism gives equivalence of the original and renamed path
problems, rather than only the forward implication of a graph embedding. -/
theorem feasible_mapIso_iff {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
    {S : Set α} (A : Termination S) (G : Graph α β) (H : Graph α' β')
    (φ : pathGraph G ≃g pathGraph H) :
    (A.mapEmbedding ⟨φ, φ.injective⟩).Feasible H ↔ A.Feasible G := by
  constructor
  · intro h
    have hback := h.mapHom φ.symm.toHom φ.symm.injective
    have hpairs : ((A.mapEmbedding ⟨φ, φ.injective⟩).mapEmbedding
        ⟨φ.symm, φ.symm.injective⟩).pairs = A.pairs := by
      change (A.pairs.image (Sym2.map φ)).image (Sym2.map φ.symm) = A.pairs
      rw [Finset.image_image]
      have hmap (p : Sym2 α) : (p.map φ).map φ.symm = p := by
        induction p using Sym2.inductionOn with
        | hf a b =>
          change s(φ.symm (φ a), φ.symm (φ b)) = s(a, b)
          rw [φ.symm_apply_apply, φ.symm_apply_apply]
      simp only [Function.comp_def, hmap, Finset.image_id']
    exact (feasible_iff_of_pairs_eq _ A G hpairs).1 hback
  · intro h
    exact h.mapHom φ.toHom φ.injective

end GraphMinor.GM02
