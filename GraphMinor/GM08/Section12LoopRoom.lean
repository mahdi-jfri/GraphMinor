module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section12CellularSectors
import GraphMinor.GM08.Section8Defs
import GraphMinor.GM08.Section10Push
import GraphMinor.Surface.Disc
import GraphMinor.GM06.DiscRegions

/-!
# Room for the cellular loops inside the original disc

A loop of a disc drawing bounds a closed disc inside the ambient disc.
Embed that configuration in the sphere and use an empty rotation sector
at the loop end. The resulting tangent disc stays inside the old loop
disc, so it pulls back into the original surface, even when the end is
on the ambient boundary. This prepares the cellular drawing used in
VIII, Section 12, page 274.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- An edge with just one end has an `O`-arc as its closure, by the
loop clause in the definition of a drawing. -/
theorem isOArc_closure_of_loop_ends {S : Type u} [TopologicalSpace S]
    {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E) {v : S}
    (hcap : closure e ∩ Γ.V = {v}) : IsOArc (closure e) := by
  rcases Γ.edge_cond e he with ⟨a, b, hab, hcap', _⟩ | ⟨_, _, hO⟩
  · have heq : ({a, b} : Set S) = {v} := hcap'.symm.trans hcap
    have ha : a = v := mem_singleton_iff.mp (heq ▸ mem_insert a {b})
    have hb : b = v := mem_singleton_iff.mp (heq ▸ mem_insert_of_mem a (mem_singleton b))
    exact False.elim (hab (ha.trans hb.symm))
  · exact hO

/-- A loop end in a disc drawing has an arbitrarily small closed disc
that touches the drawing only at that end. This supplies the empty
room for the cellular loops used in VIII, Section 12, page 274. -/
theorem exists_empty_disc_at_loop_in_disc {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (Γ : Drawing S)
    {e : Set S} (he : e ∈ Γ.E) {v : S} (hcap : closure e ∩ Γ.V = {v})
    {O : Set S} (hO : IsOpen O) (hvO : v ∈ O) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ O ∧ v ∈ discBd E ∧ E ∩ Γ.U = {v} ∧ E ∩ bd S ⊆ {v} := by
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hS
  have hf := sc.isClosedEmbedding_of_univ hS
  have hfi := hf.injective
  obtain ⟨Γ', _, hU, hV, hE, hcl, _, _⟩ := sc.exists_transport_drawing hS Γ (subset_univ _)
  obtain ⟨K, hK, -⟩ := disc_oArc univ (closure e) hS (subset_univ _)
    (isOArc_closure_of_loop_ends he hcap)
  have hK' := sc.disc_f (subset_univ K) hK.2.1
  have hcap' : closure (f '' e) ∩ Γ'.V = {f v} := by
    rw [hcl e he, hV, ← image_inter hfi, hcap, image_singleton]
  have he' : f '' e ∈ Γ'.E := hE.symm ▸ mem_image_of_mem (image f) he
  let O' := (f '' Oᶜ)ᶜ
  have hO' : IsOpen O' := (hf.isClosedMap _ hO.isClosed_compl).isOpen_compl
  have hvO' : f v ∈ O' := by
    rintro ⟨x, hx, hxv⟩
    exact hx (hfi hxv ▸ hvO)
  have hbdK' : discBd (f '' K) = closure (f '' e) := by
    rw [hK'.2, hK.2.2.1, hcl e he]
  obtain ⟨E', hE', hEK, hEO, hvE', hEΓ⟩ := exists_empty_disc_at_loop
    isClosedSurface_sphere' Γ' he' hcap' hK'.1 hbdK' hO' hvO'
  have hEΔ : E' ⊆ f '' (univ : Set S) := hEK.trans (image_mono (subset_univ K))
  have hback := hE'.image (sc.f'c.mono hEΔ) (sc.fc.mono (subset_univ _)) (sc.ff'.mono hEΔ)
  refine ⟨f' '' E', hback.1, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    by_contra hxO
    exact hEO hy ⟨f' y, hxO, sc.ff' (hEΔ hy)⟩
  · rw [hback.2]
    have hfv : f' (f v) = v := sc.f'f (mem_univ v)
    exact hfv ▸ mem_image_of_mem f' hvE'
  · ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxΓ⟩
      have hyΓ : y ∈ Γ'.U := by
        rw [hU]
        exact ⟨f' y, hxΓ, sc.ff' (hEΔ hy)⟩
      have hyv : y = f v := mem_singleton_iff.mp (hEΓ ▸ And.intro hy hyΓ)
      rw [hyv, sc.f'f (mem_univ v)]
      exact mem_singleton v
    · intro hx
      have hxv := mem_singleton_iff.mp hx
      subst x
      have hvΓ : v ∈ Γ.U := Γ.V_subset_U (hcap.symm ▸ mem_singleton v).2
      exact ⟨⟨f v, discBd_subset E' hvE', sc.f'f (mem_univ v)⟩, hvΓ⟩
  · rintro x ⟨⟨y, hy, rfl⟩, hxBd⟩
    have hxK : f' y ∈ K := by
      obtain ⟨z, hz, hzy⟩ := hEK hy
      rw [← hzy, sc.f'f (mem_univ z)]
      exact hz
    have hxcl : f' y ∈ closure e := by
      by_contra hn
      have hxb : f' y ∈ K \ closure e := ⟨hxK, hn⟩
      exact disjoint_left.mp hK.2.2.2.2.1 hxb
        (by rw [GM06.discBd_univ]; exact hxBd)
    have hyΓ : y ∈ Γ'.U := by
      rw [hU]
      exact ⟨f' y, Γ.closure_subset_U he hxcl, sc.ff' (hEΔ hy)⟩
    have hyv : y = f v := mem_singleton_iff.mp (hEΓ ▸ And.intro hy hyΓ)
    rw [hyv, sc.f'f (mem_univ v)]
    exact mem_singleton v

end GraphMinor.GM08
