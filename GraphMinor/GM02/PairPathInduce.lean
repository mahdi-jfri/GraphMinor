module

public import GraphMinor.GM02.Feasibility

/-!
# Restricting a pair path to a containing vertex set

A crossing-scheme path union is contained in its bounded boundary. Attach
membership proofs to all vertices of each path and induce its walk on
that subtype. Forgetting those proofs recovers both the original vertex
support and the original edge list. This supports compressing schemes
before their finite pattern enumeration.
-/

@[expose] public section
namespace GraphMinor.GM02
open Set SimpleGraph Classical
universe u

/-- Regard a pair path as a path on any set containing its vertices. -/
noncomputable def PairPath.induce {α : Type u} {F : SimpleGraph α} {p : Sym2 α} {S : Set α}
    (P : PairPath F p) (hS : P.vertices ⊆ S) :
    PairPath (F.induce S) (p.attachWith (fun _ ha => hS (P.endpoint_mem ha))) where
  start := ⟨P.start, hS P.walk.start_mem_support⟩
  finish := ⟨P.finish, hS P.walk.end_mem_support⟩
  ends_eq := by
    apply Sym2.map.injective Subtype.val_injective
    simpa only [Sym2.map_mk, Sym2.attachWith_map_subtypeVal] using P.ends_eq
  walk := P.walk.induce S (fun _ ha => hS ha)
  isPath := by
    apply Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce S).toHom)
    rw [Walk.map_induce]
    exact P.isPath

/-- A restricted path contains precisely the same vertices, now typed in
the containing set. -/
theorem PairPath.mem_induce_vertices {α : Type u} {F : SimpleGraph α} {p : Sym2 α} {S : Set α}
    (P : PairPath F p) (hS : P.vertices ⊆ S) (a : S) :
    a ∈ (P.induce hS).vertices ↔ a.val ∈ P.vertices := by
  change a ∈ (P.walk.induce S (fun _ ha => hS ha)).support ↔ a.val ∈ P.walk.support
  rw [Walk.support_induce]
  exact List.mem_attachWith (fun _ ha => hS ha) a

/-- Forgetting the subtype recovers the full original vertex support. -/
theorem PairPath.induce_vertices_image {α : Type u} {F : SimpleGraph α} {p : Sym2 α} {S : Set α}
    (P : PairPath F p) (hS : P.vertices ⊆ S) :
    Subtype.val '' (P.induce hS).vertices = P.vertices := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (P.mem_induce_vertices hS b).1 hb
  · intro ha
    exact ⟨⟨a, hS ha⟩, (P.mem_induce_vertices hS _).2 ha, rfl⟩

/-- The original edge list is the image of the induced edge list. -/
theorem PairPath.induce_edges_map {α : Type u} {F : SimpleGraph α} {p : Sym2 α} {S : Set α}
    (P : PairPath F p) (hS : P.vertices ⊆ S) :
    (P.induce hS).walk.edges.map (Sym2.map Subtype.val) = P.walk.edges := by
  change (P.walk.induce S (fun _ ha => hS ha)).edges.map (Sym2.map Subtype.val) = P.walk.edges
  have he := congrArg (fun q : F.Walk P.start P.finish => q.edges)
    (Walk.map_induce (s := S) P.walk (fun _ ha => hS ha))
  exact (Walk.edges_map (p := P.walk.induce S (fun _ ha => hS ha))
    (f := (SimpleGraph.Embedding.induce S).toHom)).symm.trans he

end GraphMinor.GM02
