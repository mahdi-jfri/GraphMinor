module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Surface.CircleMove
import GraphMinor.GM12.Section4ChordAvoidance
import GraphMinor.GM12.Section4ChordGeometry

/-!
# Adding a star without triple crossings

For the multiple drawings in GM V, (8.14), put a new star centre on
a short boundary arc away from all old supporting lines. Choose each
new port in its prescribed arc, avoiding the finitely many old
crossings and endpoints. New rays meet each other only at the new
centre, where no old line passes. Thus no point lies on rays of the
new star and two distinct old lines, or on two new rays and an old line.
-/

public section
namespace GraphMinor.GM05
open Set Surface GM12
universe u v

/-- The local star selection for the general-position drawings in
GM V, proof of (8.14), page 113. The port arcs are disjoint, and the
old supporting lines are distinct. -/
theorem exists_star_in_general_position {ι : Type u} [Fintype ι] {κ : Type v}
    (a b : ι → ℂ) (ha : ∀ i, ‖a i‖=1)
    (hne : ∀ i j, i≠j → line[ℝ,a i,b i]≠line[ℝ,a j,b j])
    {s₀ s₁ : ℝ} (hs : s₀<s₁) (hslen : s₁ ≤ s₀+1)
    (u v : κ → ℝ) (huv : ∀ k,u k<v k) (hlen : ∀ k,v k≤u k+1)
    (hports : Pairwise (fun k l ↦ Disjoint
      ((fun t : ℝ ↦ (ee t : ℂ)) '' Ioo (u k) (v k))
      ((fun t : ℝ ↦ (ee t : ℂ)) '' Ioo (u l) (v l)))) :
    ∃ s ∈ Ioo s₀ s₁, ∃ t : κ → ℝ,
      (∀ k,t k∈Ioo (u k) (v k) ∧ (ee (t k) : ℂ)≠(ee s : ℂ)) ∧
      (∀ i,(ee s : ℂ)∉(line[ℝ,a i,b i] : Set ℂ)) ∧
      (∀ k i,line[ℝ,(ee s : ℂ),(ee (t k) : ℂ)]≠line[ℝ,a i,b i]) ∧
      (∀ k l,k≠l → line[ℝ,(ee s : ℂ),(ee (t k) : ℂ)]≠line[ℝ,(ee s : ℂ),(ee (t l) : ℂ)]) ∧
      (∀ k i,a i∉(line[ℝ,(ee s : ℂ),(ee (t k) : ℂ)] : Set ℂ) ∧
        b i∉(line[ℝ,(ee s : ℂ),(ee (t k) : ℂ)] : Set ℂ)) ∧
      (∀ k i j,i≠j → Disjoint (line[ℝ,(ee s : ℂ),(ee (t k) : ℂ)] : Set ℂ)
        ((line[ℝ,a i,b i] : Set ℂ)∩(line[ℝ,a j,b j] : Set ℂ))) ∧
      ∀ k l i,k≠l → Disjoint
        ((line[ℝ,(ee s : ℂ),(ee (t k) : ℂ)] : Set ℂ)∩
          (line[ℝ,(ee s : ℂ),(ee (t l) : ℂ)] : Set ℂ))
        (line[ℝ,a i,b i] : Set ℂ) := by
  classical
  let X : Set ℂ := ⋃ i, ⋃ j, if i=j then ∅ else
    (line[ℝ,a i,b i] : Set ℂ)∩(line[ℝ,a j,b j] : Set ℂ)
  have hX : X.Finite := by
    refine finite_iUnion fun i ↦ finite_iUnion fun j ↦ ?_
    split_ifs with hij
    · exact finite_empty
    · exact (subsingleton_inter_of_ne_lines (hne i j hij)).finite
  let B : Set ℂ := ⋃ i, Metric.sphere (0 : ℂ) 1 ∩ (line[ℝ,a i,b i] : Set ℂ)
  have hB : B.Finite := finite_iUnion fun i ↦ finite_unit_circle_inter_line (ha i)
  obtain ⟨s,hsI,hsbad⟩ := exists_circle_port_avoiding_finite_set (hX.union hB) hs hslen
  have hsline : ∀ i,(ee s : ℂ)∉(line[ℝ,a i,b i] : Set ℂ) := by
    intro i hi
    exact hsbad (.inr (mem_iUnion.mpr ⟨i,by simpa using And.intro (Circle.norm_coe (ee s)) hi⟩))
  let Y : Set ℂ := X ∪ range a ∪ range b
  have hY : Y.Finite := (hX.union (finite_range a)).union (finite_range b)
  have hsY : (ee s : ℂ)∉Y := by
    rintro ((hx|⟨i,hi⟩)|⟨i,hi⟩)
    · exact hsbad (.inl hx)
    · exact hsline i (hi ▸ left_mem_affineSpan_pair ℝ (a i) (b i))
    · exact hsline i (hi ▸ right_mem_affineSpan_pair ℝ (a i) (b i))
  have ht : ∀ k,∃ t∈Ioo (u k) (v k),(ee t : ℂ)≠(ee s : ℂ) ∧
      Disjoint (line[ℝ,(ee s : ℂ),(ee t : ℂ)] : Set ℂ) Y := fun k ↦
    exists_chord_line_avoiding_finite_set hY (Circle.norm_coe _) hsY (huv k) (hlen k)
  choose t htI htne htdis using ht
  have hnew : ∀ k l,k≠l → line[ℝ,(ee s : ℂ),(ee (t k) : ℂ)]≠line[ℝ,(ee s : ℂ),(ee (t l) : ℂ)] := by
    intro k l hkl he
    have hm : (ee (t l) : ℂ)∈(line[ℝ,(ee s : ℂ),(ee (t k) : ℂ)] : Set ℂ) :=
      he.symm ▸ right_mem_affineSpan_pair ℝ _ _
    rcases (unit_circle_mem_line_iff (Circle.norm_coe _) (Circle.norm_coe _) (htne k).symm
      (Circle.norm_coe _)).mp hm with hc|hp
    · exact htne l hc
    · exact disjoint_left.mp (hports hkl) ⟨t k,htI k,hp.symm⟩ ⟨t l,htI l,rfl⟩
  refine ⟨s,hsI,t,fun k ↦ ⟨htI k,htne k⟩,hsline,?_,hnew,?_,?_,?_⟩
  · intro k i he
    exact hsline i (he ▸ left_mem_affineSpan_pair ℝ _ _)
  · intro k i
    exact ⟨fun hi ↦ disjoint_left.mp (htdis k) hi (.inl (.inr ⟨i,rfl⟩)),
      fun hi ↦ disjoint_left.mp (htdis k) hi (.inr ⟨i,rfl⟩)⟩
  · intro k i j hij
    exact (htdis k).mono_right fun x hx ↦ .inl (.inl (mem_iUnion.mpr ⟨i,mem_iUnion.mpr
      ⟨j,by simpa [hij] using hx⟩⟩))
  · intro k l i hkl
    apply disjoint_left.mpr
    intro x hx hxi
    have hxs : x=(ee s : ℂ) := (subsingleton_inter_of_ne_lines (hnew k l hkl)) hx
      ⟨left_mem_affineSpan_pair ℝ _ _,left_mem_affineSpan_pair ℝ _ _⟩
    exact hsline i (hxs ▸ hxi)

end GraphMinor.GM05
