module

public import GraphMinor.Surface.Dissection
import GraphMinor.Surface.SurfacePull
import GraphMinor.GM19.Section5d

/-!
# A boundary edge has only one incident face

The boundary lies in the dissection graph. Near a boundary point which
is not a vertex, the graph is one edge of the cuff. The surface interior
is connected near that point, so all incident faces must be the same
face. This permits capping a cuff by adding one face in the Euler
calculation of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

/-- The boundary of a surface lies in the edge union of any dissection.
This is used when capping the dissection in VIII (18.2). -/
theorem dissection_boundary_subset_edges {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsSurface S) {V : Set S} {E 𝓕 : Set (Set S)} (hd : IsDissection V E 𝓕) :
    bd S ⊆ ⋃₀ E := by
  intro x hxbd
  obtain ⟨Φ, hΦ, hxΦ⟩ := hd.cover.symm.subset (mem_univ x)
  have hxbdΦ : x ∈ discBd Φ := by
    by_contra hn
    exact hxbd (isInteriorPoint_of_mem_discInt hS.2.2 (hd.disc Φ hΦ) ⟨hxΦ, hn⟩)
  exact hd.bd Φ hΦ hxbdΦ

private theorem boundary_edge_neighbourhood {S : Type} [TopologicalSpace S] [T2Space S]
    (hS : IsSurface S) {V : Set S} {E 𝓕 : Set (Set S)} (hd : IsDissection V E 𝓕)
    {x : S} (hxbd : x ∈ bd S) (hxV : x ∉ V) :
    ∃ N : Set S, IsOpen N ∧ x ∈ N ∧ N ∩ ⋃₀ E ⊆ bd S := by
  have : Nonempty S := ⟨x⟩
  let C := connectedComponentIn (bd S) x
  have hC : C ∈ cuffs S := ⟨x, hxbd, rfl⟩
  have hCO : IsOArc C := (cuff_statement S hS).2.2 C hC
  have hCbd : C ⊆ bd S := connectedComponentIn_subset _ _
  have hCE : C ⊆ ⋃₀ E := hCbd.trans (dissection_boundary_subset_edges hS hd)
  obtain ⟨e, ⟨he, heC⟩, hxe⟩ := hd.graph.subset_edges hCO hCE (mem_connectedComponentIn hxbd)
  have heBd : e ⊆ bd S := heC.trans hCbd
  have hclosed : IsClosed (⋃₀ (E \ {e})) := (hd.graph.fine.sdiff).isClosed_sUnion
    (fun f hf => by obtain ⟨u, v, _, hl, _⟩ := hd.graph.edge f hf.1; exact hl.isCompact.isClosed)
  refine ⟨(⋃₀ (E \ {e}))ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨f, hf, hxf⟩
    exact hxV (hd.graph.disj e he f hf.1 (Ne.symm hf.2) ⟨hxe, hxf⟩)
  · rintro y ⟨hyN, f, hf, hyf⟩
    by_cases hfe : f = e
    · exact heBd (hfe ▸ hyf)
    · exact (hyN ⟨f, ⟨hf, hfe⟩, hyf⟩).elim

/-- Outside the vertices, a boundary point belongs to only one face of
 a dissection. This supplies the face-incidence bound after capping in
 the Euler calculation of VIII (18.2), page 286. -/
theorem dissection_faces_at_boundary_subsingleton {S : Type} [TopologicalSpace S]
    (hS : IsSurface S) {V : Set S} {E 𝓕 : Set (Set S)} (hd : IsDissection V E 𝓕)
    {x : S} (hxbd : x ∈ bd S) (hxV : x ∉ V) : {Φ ∈ 𝓕 | x ∈ Φ}.Subsingleton := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨N, hN, hxN, hNE⟩ := boundary_edge_neighbourhood hS hd hxbd hxV
  obtain ⟨B, hBsub, hBc, W, hW, hnear⟩ :=
    (GM19.isConnectedNear_compl_bd (hS.2.2 x) hxbd).1 N (hN.mem_nhds hxN)
  have hBoff : Disjoint B (⋃₀ E) := disjoint_left.mpr (fun y hy hyE =>
    (hBsub hy).1 (hNE ⟨(hBsub hy).2, hyE⟩))
  have hmeet : ∀ Φ ∈ 𝓕, x ∈ Φ → (B ∩ discInt Φ).Nonempty := by
    intro Φ hΦ hxΦ
    obtain ⟨y, hyW, hyΦ⟩ := mem_closure_iff_nhds.mp
      ((hd.disc Φ hΦ).subset_closure_discInt hxΦ) W hW
    have hybd : y ∉ bd S := fun hy =>
      hy (isInteriorPoint_of_mem_discInt hS.2.2 (hd.disc Φ hΦ) hyΦ)
    exact ⟨y, hnear ⟨hybd, hyW⟩, hyΦ⟩
  intro Φ hΦ Ψ hΨ
  by_contra hne
  obtain ⟨p, hpB, hpΦ⟩ := hmeet Φ hΦ.1 hΦ.2
  obtain ⟨q, hqB, hqΨ⟩ := hmeet Ψ hΨ.1 hΨ.2
  have hotherclosed : IsClosed (⋃₀ (𝓕 \ {Φ})) := (hd.fin.sdiff).isClosed_sUnion
    (fun Ω hΩ => (hd.disc Ω hΩ.1).isClosed)
  have hcover : B ⊆ Φ ∪ ⋃₀ (𝓕 \ {Φ}) := by
    intro y hy
    obtain ⟨Ω, hΩ, hyΩ⟩ := hd.cover.symm.subset (mem_univ y)
    by_cases hΩΦ : Ω = Φ
    · exact Or.inl (hΩΦ ▸ hyΩ)
    · exact Or.inr ⟨Ω, ⟨hΩ, hΩΦ⟩, hyΩ⟩
  obtain ⟨z, hzB, hzΦ, Ω, hΩ, hzΩ⟩ := isPreconnected_closed_iff.mp hBc
    Φ (⋃₀ (𝓕 \ {Φ})) (hd.disc Φ hΦ.1).isClosed hotherclosed hcover
    ⟨p, hpB, hpΦ.1⟩ ⟨q, hqB, Ψ, ⟨hΨ.1, Ne.symm hne⟩, hqΨ.1⟩
  have hzint : z ∈ discInt Φ := ⟨hzΦ, fun hzbd =>
    disjoint_left.mp hBoff hzB (hd.bd Φ hΦ.1 hzbd)⟩
  exact disjoint_left.mp (hd.disj Φ hΦ.1 Ω hΩ.1 (Ne.symm hΩ.2)) hzint hzΩ

end GraphMinor.GM08
