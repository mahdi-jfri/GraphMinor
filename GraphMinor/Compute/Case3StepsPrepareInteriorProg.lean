module

public import GraphMinor.Compute.Case3StepsPerimeterProg
public import GraphMinor.Compute.Case3StepsCompassVerticesProg
public import GraphMinor.Compute.Case3StepsGatherBitsProg

/-!
# Preparing the interior-member scan from the supplied wall

The program first parses the original wall perimeter. It then collects the
original compass labels and gathers perimeter bits along this inverse list.
The resulting bitset uses compact compass labels and is retained for every
member test in XIII (9.9), step 6, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Prepare the inverse compass labels and compact perimeter bitset. -/
def case3PrepareInteriorProg {h : ℕ} (h2 : 2 ≤ h) (a_W a_VK a_base r_base : ℕ) : Cmd :=
  .seq (case3PerimeterProg h2 a_W a_base r_base)
    (.seq (case3CompassVerticesProg a_VK a_base r_base)
      (case3GatherBitsProg.shift a_base r_base))

/-- Preparation retains the compact graph and member-routing data, and
costs linear vertex time for a fixed original wall height. -/
theorem case3PrepareInteriorProg_exec {w h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (hW : W.IsValid)
    (a_W a_VK a_base r_base : ℕ) (haW : a_W < a_base) (haVK : a_VK < a_base)
    (hw : 4 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    (hc : 3 + elemWallNumVerts h < 2 ^ w) (hwall : W.encList.length < 2 ^ w)
    {s : State} (hin : s.arrs a_W = W.encList)
    (hVK : s.arrs a_VK = bitSetList W.compassFinset)
    (hrank : (s.arrs (a_base + 2)).length = n) (hrn : s.regs (r_base + 14) = compassCard W) :
    ∃ s' t, Exec w (case3PrepareInteriorProg h2 a_W a_VK a_base r_base) s s' t ∧
      t ≤ parseWallCost h n + 20 * n + 13 * compassCard W + 20 ∧
      IsBitSet (case3PullbackBits (compassEmb W) W.perimeterFinset) (a_base + 20) s' ∧
      s'.arrs (a_base + 32) = (case3BoundaryVertices W.compassFinset).map Fin.val ++
        List.replicate (n - compassCard W) 0 ∧
      (∀ a, a ≠ a_base + 20 → a ≠ a_base + 32 → a ≠ a_base + 44 → a ≠ a_base + 45 →
        s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 90, s'.regs r = s.regs r) := by
  have hkw : compassCard W + 1 < 2 ^ w := by
    have hk : compassCard W ≤ n := by
      simpa only [compassCard, Fintype.card_fin] using Finset.card_le_univ W.compassFinset
    simpa only [Fintype.card_fin] using lt_of_le_of_lt (Nat.add_le_add_right hk 1) hn
  obtain ⟨s₁, t₁, hex₁, ht₁, _, hP₁, harr₁, hreg₁⟩ :=
    case3PerimeterProg_exec D W h2 hW a_W a_base r_base haW (by omega) hn hc hwall hin hrank
  obtain ⟨s₂, t₂, hex₂, ht₂, hlist₂, _, harr₂, hreg₂⟩ :=
    case3CompassVerticesProg_exec W.compassFinset a_VK a_base r_base haVK hw hn
      (s := s₁) (by rw [harr₁ a_VK (by romega) (by romega)]; exact hVK)
      (by rw [harr₁ (a_base + 2) (by romega) (by romega)]; exact hrank)
  have hP₂ : IsBitSet W.perimeterFinset 45 (s₂.unshift a_base r_base) :=
    IsBitSet.of_bitSetList _ _ _ (by
      rw [State.unshift_arrs, Nat.add_comm 45, harr₂ (a_base + 45) (by romega)]
      exact hP₁.arr_eq_bitSetList)
  have hlistlen : compassCard W ≤ ((s₂.unshift a_base r_base).arrs 32).length := by
    rw [State.unshift_arrs, Nat.add_comm 32, hlist₂, List.length_append,
      List.length_map, case3BoundaryVertices_length, List.length_replicate, compassCard]
    omega
  have hlist : ∀ i : Fin (compassCard W),
      ((s₂.unshift a_base r_base).arrs 32).getD i.1 0 = (compassEmb W i).1 := by
    intro i
    rw [State.unshift_arrs, Nat.add_comm 32]
    exact case3CompassVerticesProg_lookup W.compassFinset a_base s₂ hlist₂ i
  have hr₂ : (s₂.unshift a_base r_base).regs 14 = compassCard W := by
    rw [State.unshift_regs, Nat.add_comm 14, hreg₂ _ (by omega), hreg₁ _ (by omega)]
    exact hrn
  obtain ⟨s_sub, t₃, hex₃, ht₃, hdst, harr₃, hreg₃⟩ :=
    case3GatherBitsProg_exec (compassEmb W) W.perimeterFinset (by omega) hkw (by omega)
      hP₂ hlistlen hlist hr₂
  let s₃ := s₂.applyShifted a_base r_base s_sub
  have hsame : ∀ a, a ≠ a_base + 20 → s₃.arrs a = s₂.arrs a := by
    intro a ha
    by_cases hab : a < a_base
    · exact State.applyShifted_arrs_lt _ _ _ _ hab
    · obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (by romega : a_base ≤ a)
      subst a
      rw [Nat.add_comm a_base b, State.applyShifted_arrs_add, harr₃ b (by romega)]
      rfl
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ (Exec.shift_from a_base r_base hex₃)),
    by omega, ?_, ?_, ?_, ?_⟩
  · exact IsBitSet.of_bitSetList _ _ _ (by
      rw [show a_base + 20 = 20 + a_base by omega, State.applyShifted_arrs_add]
      exact hdst.arr_eq_bitSetList)
  · rw [hsame _ (by romega)]
    exact hlist₂
  · intro a h20 h32 h44 h45
    rw [hsame a h20, harr₂ a h32, harr₁ a h44 h45]
  · intro r hr
    by_cases hlow : r < r_base
    · rw [State.applyShifted_regs_lt _ _ _ _ hlow, hreg₂ r hr, hreg₁ r (by omega)]
    · obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (by romega : r_base ≤ r)
      subst r
      rw [Nat.add_comm r_base b, State.applyShifted_regs_add, hreg₃ b (by romega), State.unshift_regs]
      rw [hreg₂ _ (by omega), hreg₁ _ (by omega)]

end GraphMinor.Compute
