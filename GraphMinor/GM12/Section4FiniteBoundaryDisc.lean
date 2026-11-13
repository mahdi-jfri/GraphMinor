module

public import GraphMinor.Surface.Collar
import GraphMinor.GM19.DiscTouch
import GraphMinor.Surface.Wedge

/-!
# A disc meeting a boundary in finitely many prescribed points

For the four-mark discs in XII (4.5), page 253, a smaller disc must
meet the surrounding disc boundary only at its assigned marks.
Use the plane construction, which takes the convex hull of the
marks and a smaller round disc, and transfer it through the disc
chart. The plane construction is independent of the universe of
the ambient surface.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

/-- A smaller closed disc touches the original boundary precisely
at a finite nonempty prescribed set, in an arbitrary universe. -/
theorem exists_disc_touching_finite_boundary_set
    {S : Type*} [TopologicalSpace S] [T2Space S] {D N : Set S}
    (hD : IsClosedDisc D) (hN : N ⊆ discBd D) (hfin : N.Finite) (hne : N.Nonempty) :
    ∃ Q, IsClosedDisc Q ∧ Q ⊆ D ∧ Q ∩ discBd D = N ∧ N ⊆ discBd Q := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  let N₀ := h '' N
  have hunit := isClosedDisc_closedBall
  have hN₀ : N₀ ⊆ discBd (closedBall (0 : ℂ) 1) := by
    rw [hunit.2]
    rintro _ ⟨n, hn, rfl⟩
    exact c.bd ▸ mem_image_of_mem h (hN hn)
  obtain ⟨Q₀, hQ₀, hsub, hmeet, hbd⟩ :=
    GM19.IsClosedDisc.exists_touching hunit.1 hN₀ (hfin.image h) (hne.image h)
  have hgi : InjOn g Q₀ := by
    intro x hx y hy hxy
    have h' := congrArg h hxy
    rwa [c.hg (hsub hx), c.hg (hsub hy)] at h'
  obtain ⟨hQ, hQbd⟩ := Surface.isClosedDisc_image_injOn hQ₀ hQ₀.isCompact (c.gc.mono hsub) hgi
  have hgh : ∀ n ∈ N, g (h n) = n := fun n hn => c.gh (discBd_subset D (hN hn))
  refine ⟨g '' Q₀, hQ, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact c.gm (hsub hx)
  · apply Set.Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxBd⟩
      have hxS : x ∈ sphere (0 : ℂ) 1 := by
        have h' : h (g x) ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hxBd
        rwa [c.hg (hsub hx)] at h'
      have hxN : x ∈ N₀ := hmeet.subset ⟨hx, hunit.2.symm ▸ hxS⟩
      obtain ⟨n, hn, rfl⟩ := hxN
      rwa [hgh n hn]
    · intro n hn
      have hn₀ : h n ∈ Q₀ := ((hmeet.symm).subset (mem_image_of_mem h hn)).1
      exact ⟨⟨h n, hn₀, hgh n hn⟩, hN hn⟩
  · intro n hn
    rw [hQbd]
    exact ⟨h n, hbd (mem_image_of_mem h hn), hgh n hn⟩

end GraphMinor.GM12
