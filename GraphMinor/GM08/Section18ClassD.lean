module

public import GraphMinor.GM08.Section18Step
import GraphMinor.GM08.Section18Connected
import GraphMinor.GM08.Section18Sphere
import GraphMinor.GM08.Section17
import GraphMinor.Surface.Classification
import GraphMinor.Surface.AddCrosscap
import GraphMinor.Surface.NormalWord
import GraphMinor.GM07.CutBounds

/-!
# The class `𝒟(h, k)` of page 287

`𝒟(h, k)` is the union of `𝒞(Σ, k)` over all connected surfaces `Σ` with
`g(Σ) ≤ h`. Page 287: "If `Σ₁ ≅ Σ₂` then `𝒞(Σ₁, k) = 𝒞(Σ₂, k)`, and up to
homeomorphism there are only finitely many connected surfaces `Σ` with
`g(Σ) ≤ h`." Each connected surface is a model `Σ(a, b, c)`
(`classification`), and `g(Σ(a, b, c)) = 4a + 2b + c`, so only the models with
`4a + 2b + c ≤ h` occur. We use the copies of the models in the universe of
the surfaces.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v w

/-- `𝒟(h, k)`: the union of `𝒞(Σ, k)` over all connected surfaces `Σ` with
`g(Σ) ≤ h` (VIII, page 287). -/
def classD {α : Type u} {β : Type v} (h k : ℕ) : Set (Graft α β) :=
  {X | ∃ (S : Type w) (_ : TopologicalSpace S), IsSurface S ∧ ConnectedSpace S ∧
    surfaceComplexity S ≤ h ∧ X ∈ classCSurface S k}

/-- `𝒞(Σ, k)` depends only on `Σ` up to homeomorphism. -/
theorem classCSurface_congr {S : Type w} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    (e : S ≃ₜ T) {α β : Type u} (k : ℕ) :
    classCSurface (α := α) (β := β) S k = classCSurface T k := by
  ext X
  exact ⟨fun h => ⟨h.1, embedsGraft_of_homeomorph e h.2⟩,
    fun h => ⟨h.1, embedsGraft_of_homeomorph e.symm h.2⟩⟩

/-- **`𝒞(Σ, k)` is well-rooted for a connected surface `Σ` with `g(Σ) ≤ h`**,
given the steps and the two inductive hypotheses (page 287). -/
theorem isWellRooted_classCSurface_connected (hcut : CutStepStatement.{u, w})
    (hsplit : SplitStepStatement.{u, w}) {h k : ℕ}
    (hlow : ∀ k', ClassCWellRooted.{u, w} (h - 1) k')
    (hprev : 1 ≤ k → ClassCWellRooted.{u, w} h (k - 1))
    {S : Type w} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hg : surfaceComplexity S ≤ h) {α β : Type u} :
    IsWellRootedGraftClass (classCSurface (α := α) (β := β) S k) := by
  obtain ⟨a, b, c, he⟩ := classification.{w} S hS inferInstance
  by_cases h3 : 3 ≤ 3 * a + 3 * b + c
  · exact isWellRooted_classCSurface_of_steps hcut hsplit hlow hprev hS hg h3 he
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    have hc : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact isWellRooted_classCSurface_sphere hS he k
    · exact isWellRooted_classCSurface_disc he k
    · exact isWellRooted_classCSurface_cylinder he k

/-- **`𝒟(h, k)` is well-rooted**, given the steps and the two inductive
hypotheses: it is a finite union of the classes `𝒞(Σ(a, b, c), k)` by (4.2). -/
theorem isWellRooted_classD (hcut : CutStepStatement.{u, w})
    (hsplit : SplitStepStatement.{u, w}) {h k : ℕ}
    (hlow : ∀ k', ClassCWellRooted.{u, w} (h - 1) k')
    (hprev : 1 ≤ k → ClassCWellRooted.{u, w} h (k - 1)) {α β : Type u} :
    IsWellRootedGraftClass (classD.{u, u, w} (α := α) (β := β) h k) := by
  classical
  let M : ℕ × ℕ × ℕ → Type w := fun p => ULift.{w} (SurfaceModel p.1 p.2.1 p.2.2)
  let s : Finset (ℕ × ℕ × ℕ) :=
    (Finset.range (h + 1) ×ˢ Finset.range (h + 1) ×ˢ Finset.range (h + 1)).filter
      (fun p => 4 * p.1 + 2 * p.2.1 + p.2.2 ≤ h)
  have hM : ∀ p, IsSurface (M p) ∧ ConnectedSpace (M p) := fun p =>
    ⟨isSurface_of_homeo Homeomorph.ulift.symm (isSurface_model _ _ _).1,
      @GM07.connectedSpace_of_model _ _ p.1 p.2.1 p.2.2 ⟨Homeomorph.ulift⟩⟩
  have hgM : ∀ p, surfaceComplexity (M p) = 4 * p.1 + 2 * p.2.1 + p.2.2 := fun p => by
    have := (hM p).2
    rw [surfaceComplexity_eq_connected]
    exact connectedSurfaceComplexity_eq ⟨Homeomorph.ulift⟩
  refine isWellRootedGraftClass_mono ?_ (isWellRootedGraftClass_biUnion_finset s
    (𝒜 := fun p => classCSurface (α := α) (β := β) (M p) k) fun p hp => ?_)
  · rintro X ⟨S, tS, hS, hconn, hg, hX⟩
    obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{w} S hS hconn
    have hgS : surfaceComplexity S = 4 * a + 2 * b + c := by
      rw [surfaceComplexity_eq_connected]; exact connectedSurfaceComplexity_eq ⟨e⟩
    refine mem_iUnion₂.mpr ⟨(a, b, c), ?_, ?_⟩
    · simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · rw [← classCSurface_congr (e.trans Homeomorph.ulift.symm)]
      exact hX
  · have := (hM p).2
    have hp' : 4 * p.1 + 2 * p.2.1 + p.2.2 ≤ h := (Finset.mem_filter.mp hp).2
    exact isWellRooted_classCSurface_connected hcut hsplit hlow hprev (hM p).1
      (by rw [hgM]; exact hp')

end GraphMinor.GM08
