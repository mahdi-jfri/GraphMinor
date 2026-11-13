module

public import GraphMinor.Surface.Defs
public import GraphMinor.GM05.FixedPortStarFamilies
import GraphMinor.Surface.DiscPolygon
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM12.Section4ChordGeometry

/-!
# Fixed-port stars in a closed disc

For GM V, (8.14), use coordinates on each closed vertex disc.
The fixed ports become distinct unit circle points. Choose all star
centres by the fixed-port selection, draw the rays as straight chords,
and map them back. The chart preserves their intersections. Every
ray meets the disc boundary only at its centre and its prescribed port.
-/

public section
namespace GraphMinor.GM05
open Set Surface Metric GM12
universe v

/-- The actual local stars in the vertex discs of GM V, (8.14),
page 113, with all boundary ports fixed. -/
theorem exists_disc_fixed_port_stars {S : Type} [TopologicalSpace S] [T2Space S]
    {R : Set S} (hR : IsClosedDisc R) (m : ℕ) {κ : Type v} [Fintype κ]
    (p : Fin m × κ → S) (hp : ∀ q, p q ∈ discBd R) (hpi : Function.Injective p) :
    ∃ x : Fin m → S, ∃ L : Fin m × κ → Set S,
      (∀ i, x i ∈ discBd R) ∧ (∀ i j, i ≠ j → x i ≠ x j) ∧
      (∀ i q, x i ≠ p q) ∧
      (∀ q, IsLineWithEnds (L q) (x q.1) (p q) ∧ L q ⊆ R ∧
        L q ∩ discBd R = {x q.1,p q}) ∧
      (∀ i e f, e ≠ f → L (i,e) ∩ L (i,f) = {x i}) ∧
      (∀ q r, q ≠ r → (L q ∩ L r).Finite) ∧
      ∀ i j l e f g, i ≠ j → j ≠ l → i ≠ l →
        L (i,e) ∩ L (j,f) ∩ L (l,g) = ∅ := by
  classical
  obtain ⟨h,g,c⟩ := hR.exists_isChart
  let b : Fin m × κ → ℂ := fun q ↦ h (p q)
  have hb : ∀ q, ‖b q‖ = 1 := by
    intro q
    have hh : b q ∈ sphere (0 : ℂ) 1 := c.bd ▸ ⟨p q,hp q,rfl⟩
    simpa only [mem_sphere,dist_zero_right] using hh
  have hbD : ∀ q, b q ∈ closedBall (0 : ℂ) 1 := fun q ↦ c.hm (discBd_subset R (hp q))
  have hbi : Function.Injective b := by
    intro q r he
    exact hpi (c.gh.injOn (discBd_subset R (hp q)) (discBd_subset R (hp r)) he)
  obtain ⟨s,hsI,hsQ,hsne,hline,hthree⟩ := exists_fixed_port_star_family m b hb hbi
    (finite_range b) (fun q ↦ mem_range_self q) (s₀ := 0) (s₁ := 1) zero_lt_one (by norm_num)
  let a : Fin m → ℂ := fun i ↦ ee (s i)
  have ha : ∀ i, ‖a i‖ = 1 := fun i ↦ Circle.norm_coe _
  have haD : ∀ i, a i ∈ closedBall (0 : ℂ) 1 := fun i ↦ by simp [ha i]
  have hab : ∀ q, a q.1 ≠ b q := by
    intro q he
    apply hsQ q.1
    change a q.1 ∈ range b
    rw [he]
    exact mem_range_self q
  let T : Fin m × κ → Set ℂ := fun q ↦ segment ℝ (a q.1) (b q)
  have hT : ∀ q, IsLineWithEnds (T q) (a q.1) (b q) ∧ T q ⊆ closedBall 0 1 ∧
      T q ∩ sphere 0 1 = {a q.1,b q} := fun q ↦ unit_chord_geometry (ha q.1) (hb q) (hab q)
  have hTline : ∀ q, T q ⊆ (line[ℝ,a q.1,b q] : Set ℂ) := fun q ↦
    (line[ℝ,a q.1,b q]).convex.segment_subset (left_mem_affineSpan_pair ℝ _ _) (right_mem_affineSpan_pair ℝ _ _)
  let x : Fin m → S := fun i ↦ g (a i)
  let L : Fin m × κ → Set S := fun q ↦ g '' T q
  have hgport : ∀ q, g (b q) = p q := fun q ↦ c.gh (discBd_subset R (hp q))
  have hx : ∀ i, x i ∈ discBd R := by
    intro i
    rw [← c.g_sphere]
    exact ⟨a i,by simp [ha i],rfl⟩
  have hxne : ∀ i j, i ≠ j → x i ≠ x j := by
    intro i j hij he
    exact hsne i j hij (congrArg (fun z ↦ z) (c.injOn (haD i) (haD j) he))
  have hxport : ∀ i q, x i ≠ p q := by
    intro i q he
    have hcoords : a i = b q := c.injOn (haD i) (hbD q) (he.trans (hgport q).symm)
    apply hsQ i
    change a i ∈ range b
    rw [hcoords]
    exact mem_range_self q
  refine ⟨x,L,hx,hxne,hxport,?_,?_,?_,?_⟩
  · intro q
    have hl := (hT q).1.image_injOn (c.gc.mono (hT q).2.1) (c.injOn.mono (hT q).2.1)
    refine ⟨by simpa only [hgport q] using hl,c.g_subset (hT q).2.1,?_⟩
    change (g '' T q) ∩ discBd R = {g (a q.1),p q}
    rw [← c.g_sphere,← c.g_inter (hT q).2.1 sphere_subset_closedBall,(hT q).2.2,image_pair,hgport q]
  · intro i e f hef
    have hneq := hline i i e f (fun he ↦ hef (congrArg Prod.snd he))
    have hcap : T (i,e) ∩ T (i,f) = {a i} := by
      apply subset_antisymm
      · intro z hz
        exact (subsingleton_inter_of_ne_lines hneq) ⟨hTline (i,e) hz.1,hTline (i,f) hz.2⟩
          ⟨left_mem_affineSpan_pair ℝ _ _,left_mem_affineSpan_pair ℝ _ _⟩
      · rintro z rfl
        exact ⟨left_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩
    change (g '' T (i,e)) ∩ (g '' T (i,f)) = {g (a i)}
    rw [← c.g_inter (hT (i,e)).2.1 (hT (i,f)).2.1,hcap,image_singleton]
  · rintro ⟨i,e⟩ ⟨j,f⟩ hne
    change (g '' T (i,e) ∩ g '' T (j,f)).Finite
    rw [← c.g_inter (hT (i,e)).2.1 (hT (j,f)).2.1]
    exact (finite_chord_inter_of_ne_lines (hline i j e f hne)).image g
  · intro i j l e f k hij hjl hil
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨⟨⟨z₁,hz₁,h₁⟩,⟨z₂,hz₂,h₂⟩⟩,⟨z₃,hz₃,h₃⟩⟩
    have he₂ : z₂ = z₁ := c.injOn ((hT (j,f)).2.1 hz₂) ((hT (i,e)).2.1 hz₁) (h₂.trans h₁.symm)
    have he₃ : z₃ = z₁ := c.injOn ((hT (l,k)).2.1 hz₃) ((hT (i,e)).2.1 hz₁) (h₃.trans h₁.symm)
    subst z₂
    subst z₃
    exact hthree i j l e f k hij hjl hil z₁
      ⟨hTline (i,e) hz₁,hTline (j,f) hz₂,hTline (l,k) hz₃⟩

end GraphMinor.GM05
