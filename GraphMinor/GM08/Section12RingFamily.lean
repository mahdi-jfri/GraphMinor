module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section12Rings
import GraphMinor.GM08.Section9Foundation

/-!
# A disjoint family of minimal rings for the disc foundation

Apply (6.5) repeatedly as on page 267 of VIII. Each application shrinks
two rings, so a pair already disjoint stays disjoint. Since there are
only finitely many pairs, minimizing the number of intersecting pairs
produces a family with no intersecting pair. Minimality of each ring
is preserved at every step.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The repeated uncrossing assertion on page 267 of VIII: the bosses
chosen for a foundation have minimal rings bounding disjoint open
discs. This supplies the ring family used in Section 12. -/
theorem exists_disjoint_minimal_ring_family {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {t : ℕ} (C : Fin t → DiscCircuit D Δ) (hC : ∀ i, IsBoss D Δ (C i))
    (hdis : Pairwise fun i j => Disjoint (bossDelta D Δ (C i)) (bossDelta D Δ (C j))) :
    ∃ F : Fin t → Set S, (∀ i, IsMinimalCRing (C i) (F i)) ∧
      Pairwise (fun i j => BoundDisjointOpenDiscs Δ (F i) (F j)) := by
  classical
  let bad : (Fin t → Set S) → Set (Fin t × Fin t) :=
    fun F => {p | p.1 ≠ p.2 ∧ ¬ BoundDisjointOpenDiscs Δ (F p.1) (F p.2)}
  have hex : ∃ n : ℕ, ∃ F : Fin t → Set S,
      (∀ i, IsMinimalCRing (C i) (F i)) ∧ (bad F).ncard = n := by
    choose F hF using fun i => (C i).exists_isMinimalCRing hΔ hbd
    exact ⟨_, F, hF, rfl⟩
  obtain ⟨F, hF, hcard⟩ := Nat.find_spec hex
  refine ⟨F, hF, fun i j hij => ?_⟩
  by_contra hbad
  obtain ⟨G₁, G₂, hG₁, hG₂, he₁, he₂, hdG⟩ :=
    uncross_disjoint_boss_rings hΔ hDU hbd (hC i) (hC j) (hF i) (hF j) (hdis hij)
  let F' : Fin t → Set S := fun a => if a = i then G₁ else if a = j then G₂ else F a
  have hF' : ∀ a, IsMinimalCRing (C a) (F' a) := by
    intro a
    by_cases hai : a = i
    · subst a
      simpa only [F', ite_eq_left rfl, ite_true] using hG₁
    · by_cases haj : a = j
      · subst a
        simpa only [F', ite_eq_right hai, ite_eq_left rfl, ite_true] using hG₂
      · simpa only [F', ite_eq_right hai, ite_eq_right haj] using hF a
  have henc : ∀ a, OArcEncloses Δ (F a) (F' a) := by
    intro a
    by_cases hai : a = i
    · subst a
      simpa only [F', ite_eq_left rfl, ite_true] using he₁
    · by_cases haj : a = j
      · subst a
        simpa only [F', ite_eq_right hai, ite_eq_left rfl, ite_true] using he₂
      · simp only [F', ite_eq_right hai, ite_eq_right haj]
        exact fun x hx => False.elim (hx.2 hx.1)
  have hsub : bad F' ⊆ bad F := by
    rintro ⟨a, b⟩ ⟨hab, hn⟩
    refine ⟨hab, fun hd => hn ?_⟩
    exact boundDisjointOpenDiscs_of_enclosed hΔ
      (hF a).1.1 (hF b).1.1 (hF' a).1.1 (hF' b).1.1
      (hF a).1.2.1 (hF b).1.2.1 (hF' a).1.2.1 (hF' b).1.2.1 (henc a) (henc b) hd
  have hremoved : (i, j) ∉ bad F' := by
    rintro ⟨-, hn⟩
    apply hn
    simpa only [F', ite_eq_left rfl, ite_eq_right hij.symm, ite_true] using hdG
  have hstrict : bad F' ⊂ bad F := by
    refine ⟨hsub, fun hrev => ?_⟩
    exact hremoved (hrev ⟨hij, hbad⟩)
  have hlt := ncard_lt_ncard hstrict (toFinite (bad F))
  have hmin := Nat.find_min' hex (show ∃ G : Fin t → Set S,
      (∀ i, IsMinimalCRing (C i) (G i)) ∧ (bad G).ncard = (bad F').ncard from
    ⟨F', hF', rfl⟩)
  omega

end GraphMinor.GM08
