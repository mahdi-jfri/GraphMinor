module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.ExteriorK5
import GraphMinor.LRPlanarity.ExteriorK5Assembly
import GraphMinor.LRPlanarity.ExteriorK5Boundary
import GraphMinor.LRPlanarity.ExteriorK5Spokes
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.Surface.SurfaceGraph

/-!
# The complete graph from alternating exterior arcs

Part IV, Section 7c of the planarity note constructs four boundary sides,
four interior spokes, and two exterior arcs. Their ten lines give a plane
complete graph on the center and the four ports.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Topology

/-- Part IV, Section 7c: the four boundary sides, the four radial spokes,
and the two alternating exterior arcs form a plane complete graph on five
vertices. -/
theorem exteriorK5Statement : ExteriorK5Statement := by
  intro D A B a c b d hD hcross hA hB hAD hBD hAB
  have hbd : Surface.discBd D = frontier D :=
    (Surface.subBd_eq_discBd_complex hD).symm.trans (Surface.subBd_eq_frontier D)
  rw [← hbd] at hcross
  obtain ⟨P, Q, R, S, hP, hQ, hR, hS, hcover, hPQ, hQR, hRS, hSP, hPR, hQS⟩ :=
    exists_boundary_four_cycle hD.isOArc_discBd hcross
  obtain ⟨ha, hb, hc, hd, hac, h_b_d, hab, had, hcb, hcd, hcomp⟩ := hcross
  let port : Fin 4 → ℂ := ![a, b, c, d]
  have hport : ∀ i, port i ∈ Surface.discBd D := by
    intro i
    fin_cases i <;> assumption
  have hpInj : Function.Injective port := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [port, Ne.symm]
  obtain ⟨h, g, chart⟩ := hD.exists_isChart
  obtain ⟨z, spoke, hz, hspoke, hss⟩ := exists_disc_spokes chart port hport hpInj
  let pt : Fin 5 → ℂ := Fin.cons z port
  have hzPort : z ∉ range port := by
    rintro ⟨i, rfl⟩
    exact hz.2 (hport i)
  have ptInj : Function.Injective pt := Fin.cons_injective_of_injective hzPort hpInj
  let W : Set ℂ := range pt
  have hzW : z ∈ W := ⟨0, rfl⟩
  have hpW : ∀ i, port i ∈ W := fun i => ⟨i.succ, rfl⟩
  have haW : a ∈ W := hpW 0
  have hbW : b ∈ W := hpW 1
  have hcW : c ∈ W := hpW 2
  have hdW : d ∈ W := hpW 3
  have hPbd : P ⊆ Surface.discBd D := by
    intro x hx
    rw [← hcover]
    exact Or.inl (Or.inl (Or.inl hx))
  have hQbd : Q ⊆ Surface.discBd D := by
    intro x hx
    rw [← hcover]
    exact Or.inl (Or.inl (Or.inr hx))
  have hRbd : R ⊆ Surface.discBd D := by
    intro x hx
    rw [← hcover]
    exact Or.inl (Or.inr hx)
  have hSbd : S ⊆ Surface.discBd D := by
    intro x hx
    rw [← hcover]
    exact Or.inr hx
  have bdD := Surface.discBd_subset D
  have hPD := hPbd.trans bdD
  have hQD := hQbd.trans bdD
  have hRD := hRbd.trans bdD
  have hSD := hSbd.trans bdD
  have hZ0D := (hspoke 0).2.1
  have hZ1D := (hspoke 1).2.1
  have hZ2D := (hspoke 2).2.1
  have hZ3D := (hspoke 3).2.1
  have noZ : ∀ X, X ⊆ Surface.discBd D → z ∉ X :=
    fun X hX hx => hz.2 (hX hx)
  have hzP := noZ P hPbd
  have hzQ := noZ Q hQbd
  have hzR := noZ R hRbd
  have hzS := noZ S hSbd
  have hzA : z ∉ A := by
    intro hx
    have hm : z ∈ ({a, c} : Set ℂ) := hAD ▸ ⟨hx, hz.1⟩
    rcases hm with rfl | rfl
    · exact hz.2 ha
    · exact hz.2 hc
  have hzB : z ∉ B := by
    intro hx
    have hm : z ∈ ({b, d} : Set ℂ) := hBD ▸ ⟨hx, hz.1⟩
    rcases hm with rfl | rfl
    · exact hz.2 hb
    · exact hz.2 hd
  have hAcB : a ∉ B := fun hm => disjoint_left.mp hAB hA.left_mem hm
  have hCcB : c ∉ B := fun hm => disjoint_left.mp hAB hA.right_mem hm
  have hBcA : b ∉ A := fun hm => disjoint_left.mp hAB hm hB.left_mem
  have hDcA : d ∉ A := fun hm => disjoint_left.mp hAB hm hB.right_mem
  have hcP : c ∉ P := fun hm => hcb (mem_singleton_iff.mp (hPQ ▸ ⟨hm, hQ.right_mem⟩))
  have hdP : d ∉ P := fun hm => disjoint_left.mp hPR hm hR.right_mem
  have haQ : a ∉ Q := fun hm => hab (mem_singleton_iff.mp (hPQ ▸ ⟨hP.left_mem, hm⟩))
  have hdQ : d ∉ Q := fun hm => disjoint_left.mp hQS hm hS.left_mem
  have haR : a ∉ R := fun hm => disjoint_left.mp hPR hP.left_mem hm
  have hbR : b ∉ R := fun hm => hcb.symm (mem_singleton_iff.mp (hQR ▸ ⟨hQ.left_mem, hm⟩))
  have hbS : b ∉ S := fun hm => disjoint_left.mp hQS hQ.left_mem hm
  have hcS : c ∉ S := fun hm => hcd (mem_singleton_iff.mp (hRS ▸ ⟨hR.left_mem, hm⟩))
  have not_spoke : ∀ i j, i ≠ j → port j ∉ spoke i := by
    intro i j hij hm
    have he : port j = port i := mem_singleton_iff.mp ((hspoke i).2.2 ▸ ⟨hm, hport j⟩)
    exact hij (hpInj he).symm
  have hZ0b : b ∉ spoke 0 := not_spoke 0 1 (by decide)
  have hZ0c : c ∉ spoke 0 := not_spoke 0 2 (by decide)
  have hZ0d : d ∉ spoke 0 := not_spoke 0 3 (by decide)
  have hZ1a : a ∉ spoke 1 := not_spoke 1 0 (by decide)
  have hZ1c : c ∉ spoke 1 := not_spoke 1 2 (by decide)
  have hZ1d : d ∉ spoke 1 := not_spoke 1 3 (by decide)
  have hZ2a : a ∉ spoke 2 := not_spoke 2 0 (by decide)
  have hZ2b : b ∉ spoke 2 := not_spoke 2 1 (by decide)
  have hZ2d : d ∉ spoke 2 := not_spoke 2 3 (by decide)
  have hZ3a : a ∉ spoke 3 := not_spoke 3 0 (by decide)
  have hZ3b : b ∉ spoke 3 := not_spoke 3 1 (by decide)
  have hZ3c : c ∉ spoke 3 := not_spoke 3 2 (by decide)
  let arc : Fin 10 → Set ℂ :=
    ![spoke 0, spoke 1, spoke 2, spoke 3, P, Q, R, S, A, B]
  apply planeEmbedding_of_complete_five_arcs pt arc ptInj
  · intro i
    fin_cases i <;>
      first
      | exact (hspoke 0).1
      | exact (hspoke 1).1
      | exact (hspoke 2).1
      | exact (hspoke 3).1
      | exact hP
      | exact hQ
      | exact hR
      | exact hS.symm
      | exact hA
      | exact hB
  · intro i w hw
    fin_cases i <;> fin_cases w <;>
      dsimp [arc, pt, port, completeFiveEnds] at hw ⊢
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | contradiction
  · have hssW : ∀ i j, i ≠ j → spoke i ∩ spoke j ⊆ W := by
      intro i j hij
      rw [hss i j hij]
      exact singleton_subset_iff.mpr hzW
    have hsbW : ∀ i X, X ⊆ Surface.discBd D → spoke i ∩ X ⊆ W := by
      intro i X hX x hx
      have he : x = port i :=
        mem_singleton_iff.mp ((hspoke i).2.2 ▸ ⟨hx.1, hX hx.2⟩)
      exact he ▸ hpW i
    have hAW : ∀ X, X ⊆ D → X ∩ A ⊆ W := by
      intro X hX x hx
      have hm : x ∈ ({a, c} : Set ℂ) := hAD ▸ ⟨hx.2, hX hx.1⟩
      rcases hm with rfl | rfl
      · exact haW
      · exact hcW
    have hBW : ∀ X, X ⊆ D → X ∩ B ⊆ W := by
      intro X hX x hx
      have hm : x ∈ ({b, d} : Set ℂ) := hBD ▸ ⟨hx.2, hX hx.1⟩
      rcases hm with rfl | rfl
      · exact hbW
      · exact hdW
    have hPQW : P ∩ Q ⊆ W := hPQ ▸ singleton_subset_iff.mpr hbW
    have hQRW : Q ∩ R ⊆ W := hQR ▸ singleton_subset_iff.mpr hcW
    have hRSW : R ∩ S ⊆ W := hRS ▸ singleton_subset_iff.mpr hdW
    have hPSW : P ∩ S ⊆ W := by
      rw [inter_comm, hSP]
      exact singleton_subset_iff.mpr haW
    have hPRW : P ∩ R ⊆ W := by rw [hPR.inter_eq]; exact empty_subset _
    have hQSW : Q ∩ S ⊆ W := by rw [hQS.inter_eq]; exact empty_subset _
    have hABW : A ∩ B ⊆ W := by rw [hAB.inter_eq]; exact empty_subset _
    have ordered : ∀ i j : Fin 10, i < j → arc i ∩ arc j ⊆ W := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      all_goals dsimp [arc]
      all_goals first
        | exact hssW _ _ (by decide)
        | exact hsbW _ _ (by assumption)
        | exact hAW _ (by assumption)
        | exact hBW _ (by assumption)
        | exact hPQW
        | exact hQRW
        | exact hRSW
        | exact hPSW
        | exact hPRW
        | exact hQSW
        | exact hABW
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact ordered i j hij
    · rw [inter_comm]
      exact ordered j i hij

/-- Part IV, Section 7c: disjoint exterior lines cannot have alternating
ports on a disc boundary. The ten constructed edges contradict Euler's
bound for five vertices. -/
theorem not_pairsCrossOn_of_exterior_lines {D A B : Set ℂ} {a c b d : ℂ}
    (hD : Surface.IsClosedDisc D)
    (hA : Surface.IsLineWithEnds A a c) (hB : Surface.IsLineWithEnds B b d)
    (hAD : A ∩ D = {a, c}) (hBD : B ∩ D = {b, d}) (hAB : Disjoint A B) :
    ¬ Surface.PairsCrossOn (frontier D) a c b d := by
  intro hcross
  exact not_planeEmbedding_K5 (exteriorK5Statement D A B a c b d hD hcross hA hB hAD hBD hAB)

end GraphMinor.LRPlanarity
