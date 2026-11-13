module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.Section14Sim

/-!
# Mapping a simulation through a vertex identification

A vertex map may identify host vertices within a branch, or with unused
vertices. It preserves a simulation if the images of distinct branches
remain disjoint. Selected edge ends already belong to branches, so no
new incidences between different branches are created. Map the connected
branch subgraphs to prove connectivity. This is used to remove collar
leaves in the proof of VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v u' v' w

private theorem connected_map {α : Type u} {β : Type v} {γ : Type w}
    {K : Graph α β} (f : α → γ) (hK : GraphConnected K) : GraphConnected (K.map f) := by
  obtain ⟨⟨x₀, hx₀⟩, hwalk⟩ := hK
  refine ⟨⟨f x₀, mem_image_of_mem f hx₀⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hxy := hwalk x hx y hy
  clear hx hy
  induction hxy with
  | refl => exact .refl
  | tail _ hadj ih => exact ih.tail (hadj.map f)

/-- A host vertex identification preserves a simulation when its branch
images remain disjoint. This is the quotient step for the collar leaves
in VIII (17.2), page 284. -/
theorem IsGraphSimulation.map_host_of_disjoint_images
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'} {ε : Type v'}
    {H : Graph δ ε} {G : Graph α β} {ηv : δ → Set α} {ηe : ε → β}
    (h : IsGraphSimulation H G ηv ηe) (f : α → γ)
    (hdis : ∀ a ∈ V(H), ∀ b ∈ V(H), a ≠ b → Disjoint (f '' ηv a) (f '' ηv b)) :
    IsGraphSimulation H (G.map f) (fun a => f '' ηv a) ηe := by
  have hmem : ∀ a ∈ V(H), ∀ e ∈ E(H), ∀ x, G.Inc (ηe e) x →
      f x ∈ f '' ηv a → x ∈ ηv a := by
    intro a ha e he x hinc hx
    obtain ⟨b, hb, _, hxb⟩ := exists_inc_and_mem_eta_of_inc h he hinc
    by_cases hab : a = b
    · exact hab.symm ▸ hxb
    · exact False.elim (disjoint_left.mp (hdis a ha b hb hab) hx (mem_image_of_mem f hxb))
  refine {
    vertex_nonempty := fun a ha => (h.vertex_nonempty a ha).image f
    vertex_subset := fun a ha => image_mono (h.vertex_subset a ha)
    edge_mem := fun e he => h.edge_mem e he
    vertex_disjoint := hdis
    edge_injOn := h.edge_injOn
    inc_iff := ?_
    isLoopAt_iff := ?_
    connected := ?_ }
  · intro a ha e he
    constructor
    · intro hinc
      obtain ⟨x, hx, hxe⟩ := (h.inc_iff a ha e he).mp hinc
      exact ⟨f x, mem_image_of_mem f hx, hxe.map f⟩
    · rintro ⟨z, hz, hze⟩
      obtain ⟨x, hxe, rfl⟩ := (Graph.map_inc f).mp hze
      exact (h.inc_iff a ha e he).mpr ⟨x, hmem a ha e he x hxe hz, hxe⟩
  · intro a ha e he
    constructor
    · intro hloop z hze
      obtain ⟨x, hxe, rfl⟩ := (Graph.map_inc f).mp hze
      exact mem_image_of_mem f ((h.isLoopAt_iff a ha e he).mp hloop x hxe)
    · intro hloop
      apply (h.isLoopAt_iff a ha e he).mpr
      intro x hxe
      exact hmem a ha e he x hxe (hloop (f x) (hxe.map f))
  · intro a ha
    obtain ⟨K, hKG, hKV, hconn⟩ := h.connected a ha
    refine ⟨K.map f, ?_, ?_, connected_map f hconn⟩
    · refine (hKG.map f).trans ?_
      refine { vertexSet_mono := fun _ hx => hx, isLink_mono := ?_ }
      rintro e x y ⟨u, v, huv, rfl, rfl⟩
      exact ⟨huv.1.map f, huv.2⟩
    · change f '' V(K) = f '' ηv a
      rw [hKV]

end GraphMinor.GM08
