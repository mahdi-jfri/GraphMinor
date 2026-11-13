module

public import GraphMinor.Surface.CircleMove
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM12.Section4ChordAvoidance
import GraphMinor.GM12.Section4ChordGeometry

/-!
# A star through fixed boundary ports

For the drawings in GM V, (8.14), the edge middles fix the ports on
a vertex disc. Only the star centre needs to move. A circle chord has
no third circle point, so each new port misses every old chord line.
Exclude the finitely many centre positions that would send a new ray
through an old crossing. The resulting star creates no triple meeting.
-/

public section
namespace GraphMinor.GM05
open Set Surface GM12
universe u v

/-- Choose a star centre for fixed distinct boundary ports while
avoiding old double crossings, for GM V, (8.14), page 113. -/
theorem exists_fixed_port_star {ι : Type u} [Fintype ι] {κ : Type v} [Fintype κ]
    (a b : ι → ℂ) (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1)
    (hab : ∀ i, a i ≠ b i)
    (hne : ∀ i j, i ≠ j → line[ℝ,a i,b i] ≠ line[ℝ,a j,b j])
    (p : κ → ℂ) (hp : ∀ k, ‖p k‖ = 1) (hpi : Function.Injective p)
    (hpa : ∀ k i, p k ≠ a i) (hpb : ∀ k i, p k ≠ b i)
    {Q : Set ℂ} (hQ : Q.Finite) (hpQ : ∀ k, p k ∈ Q)
    {s₀ s₁ : ℝ} (hs : s₀ < s₁) (hslen : s₁ ≤ s₀ + 1) :
    ∃ s ∈ Ioo s₀ s₁, (ee s : ℂ) ∉ Q ∧
      (∀ i, (ee s : ℂ) ∉ (line[ℝ,a i,b i] : Set ℂ)) ∧
      (∀ k, (ee s : ℂ) ≠ p k) ∧
      (∀ k l, k ≠ l → line[ℝ,(ee s : ℂ),p k] ≠ line[ℝ,(ee s : ℂ),p l]) ∧
      (∀ k i, line[ℝ,(ee s : ℂ),p k] ≠ line[ℝ,a i,b i]) ∧
      (∀ k i j, i ≠ j → Disjoint (line[ℝ,(ee s : ℂ),p k] : Set ℂ)
        ((line[ℝ,a i,b i] : Set ℂ) ∩ (line[ℝ,a j,b j] : Set ℂ))) ∧
      ∀ k l i, k ≠ l → Disjoint
        ((line[ℝ,(ee s : ℂ),p k] : Set ℂ) ∩ (line[ℝ,(ee s : ℂ),p l] : Set ℂ))
        (line[ℝ,a i,b i] : Set ℂ) := by
  classical
  have hport : ∀ k i, p k ∉ (line[ℝ,a i,b i] : Set ℂ) := by
    intro k i hm
    exact ((unit_circle_mem_line_iff (ha i) (hb i) (hab i) (hp k)).mp hm).elim (hpa k i) (hpb k i)
  let X : Set ℂ := ⋃ i, ⋃ j, if i = j then ∅ else
    (line[ℝ,a i,b i] : Set ℂ) ∩ (line[ℝ,a j,b j] : Set ℂ)
  have hX : X.Finite := by
    refine finite_iUnion fun i ↦ finite_iUnion fun j ↦ ?_
    split_ifs with hij
    · exact finite_empty
    · exact (subsingleton_inter_of_ne_lines (hne i j hij)).finite
  have hpX : ∀ k, p k ∉ X := by
    intro k hh
    obtain ⟨i,j,hij⟩ := mem_iUnion₂.mp hh
    split_ifs at hij with he
    · exact hij
    · exact hport k i hij.1
  let L : Set ℂ := ⋃ i, Metric.sphere (0 : ℂ) 1 ∩ (line[ℝ,a i,b i] : Set ℂ)
  let Y : Set ℂ := ⋃ k, ⋃ x ∈ X,
    Metric.sphere (0 : ℂ) 1 ∩ (line[ℝ,p k,x] : Set ℂ)
  have hL : L.Finite := finite_iUnion fun i ↦ finite_unit_circle_inter_line (ha i)
  have hY : Y.Finite := finite_iUnion fun k ↦ hX.biUnion fun x _ ↦ finite_unit_circle_inter_line (hp k)
  obtain ⟨s,hsI,hsbad⟩ := exists_circle_port_avoiding_finite_set ((hQ.union hL).union hY) hs hslen
  have hsQ : (ee s : ℂ) ∉ Q := fun h ↦ hsbad (.inl (.inl h))
  have hsline : ∀ i, (ee s : ℂ) ∉ (line[ℝ,a i,b i] : Set ℂ) := by
    intro i hi
    exact hsbad (.inl (.inr (mem_iUnion.mpr ⟨i,by simpa using And.intro (Circle.norm_coe (ee s)) hi⟩)))
  have hsp : ∀ k, (ee s : ℂ) ≠ p k := fun k he ↦ hsQ (he ▸ hpQ k)
  have hnew : ∀ k l, k ≠ l → line[ℝ,(ee s : ℂ),p k] ≠ line[ℝ,(ee s : ℂ),p l] := by
    intro k l hkl he
    have hm : p l ∈ (line[ℝ,(ee s : ℂ),p k] : Set ℂ) := he.symm ▸ right_mem_affineSpan_pair ℝ _ _
    rcases (unit_circle_mem_line_iff (Circle.norm_coe _) (hp k) (hsp k) (hp l)).mp hm with hh | hh
    · exact hsp l hh.symm
    · exact hkl (hpi hh.symm)
  have havoid : ∀ k, Disjoint (line[ℝ,(ee s : ℂ),p k] : Set ℂ) X := by
    intro k
    apply disjoint_left.mpr
    intro x hx hxX
    have hx' : x ∈ (line[ℝ,p k,(ee s : ℂ)] : Set ℂ) := by
      rwa [Set.pair_comm] at hx
    have hxp : x ≠ p k := fun he ↦ hpX k (he ▸ hxX)
    have heq := affineSpan_pair_eq_of_right_mem_of_ne hx' hxp
    have hsx : (ee s : ℂ) ∈ (line[ℝ,p k,x] : Set ℂ) := by
      rw [heq]
      exact right_mem_affineSpan_pair ℝ _ _
    exact hsbad (.inr (mem_iUnion.mpr ⟨k,mem_iUnion₂.mpr ⟨x,hxX,
      by simpa using And.intro (Circle.norm_coe (ee s)) hsx⟩⟩))
  refine ⟨s,hsI,hsQ,hsline,hsp,hnew,?_,?_,?_⟩
  · intro k i he
    exact hport k i (he ▸ right_mem_affineSpan_pair ℝ _ _)
  · intro k i j hij
    exact (havoid k).mono_right fun x hx ↦ mem_iUnion₂.mpr ⟨i,j,by simpa [hij] using hx⟩
  · intro k l i hkl
    apply disjoint_left.mpr
    intro x hx hxi
    have hxs : x = (ee s : ℂ) := (subsingleton_inter_of_ne_lines (hnew k l hkl)) hx
      ⟨left_mem_affineSpan_pair ℝ _ _,left_mem_affineSpan_pair ℝ _ _⟩
    exact hsline i (hxs ▸ hxi)

end GraphMinor.GM05
