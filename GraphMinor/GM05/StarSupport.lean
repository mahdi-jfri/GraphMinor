module

public import GraphMinor.Surface.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Supports of vertex stars

The local star used in GM V, (8.14), consists of its centre and its
rays. Keeping the centre explicitly includes isolated vertices.
The rays share the centre, so the support is connected. A finite
family of closed rays has a closed support.
-/

@[expose] public section
namespace GraphMinor.GM05
open Set Surface

/-- The point set of a local vertex star in the copy construction
for GM V, (8.14), page 113, including its isolated centre. -/
def starSupport {S ι κ : Type*} (x : ι → S) (L : ι × κ → Set S) (i : ι) : Set S :=
  {x i} ∪ ⋃ e, L (i,e)

/-- The centre belongs to its star support. -/
theorem centre_mem_starSupport {S ι κ : Type*} (x : ι → S) (L : ι × κ → Set S) (i : ι) :
    x i ∈ starSupport x L i := Or.inl rfl

/-- Each ray belongs to its star support. -/
theorem ray_subset_starSupport {S ι κ : Type*} (x : ι → S) (L : ι × κ → Set S) (i : ι) (e : κ) :
    L (i,e) ⊆ starSupport x L i := fun _ hx ↦ Or.inr (mem_iUnion.mpr ⟨e,hx⟩)

/-- Connected rays with a common centre form a connected star,
including when there are no rays. -/
theorem isPreconnected_starSupport {S ι κ : Type*} [TopologicalSpace S]
    (x : ι → S) (L : ι × κ → Set S) (i : ι)
    (hL : ∀ e, IsPreconnected (L (i,e))) (hx : ∀ e, x i ∈ L (i,e)) :
    IsPreconnected (starSupport x L i) := by
  have h := isPreconnected_sUnion (x i) (insert {x i} (range fun e ↦ L (i,e)))
    (by
      rintro A (rfl | ⟨e,rfl⟩)
      · rfl
      · exact hx e)
    (by
      rintro A (rfl | ⟨e,rfl⟩)
      · exact isPreconnected_singleton
      · exact hL e)
  simpa [starSupport] using h

/-- Finite stars with closed rays have closed supports. -/
theorem isClosed_starSupport {S ι κ : Type*} [TopologicalSpace S] [T1Space S] [Finite κ]
    (x : ι → S) (L : ι × κ → Set S) (i : ι) (hL : ∀ e, IsClosed (L (i,e))) :
    IsClosed (starSupport x L i) :=
  isClosed_singleton.union (isClosed_iUnion_of_finite hL)

/-- A disc containing the centre and every ray contains the star. -/
theorem starSupport_subset {S ι κ : Type*} (x : ι → S) (L : ι × κ → Set S) (i : ι)
    {R : Set S} (hx : x i ∈ R) (hL : ∀ e, L (i,e) ⊆ R) : starSupport x L i ⊆ R :=
  union_subset (singleton_subset_iff.mpr hx) (iUnion_subset hL)

end GraphMinor.GM05
