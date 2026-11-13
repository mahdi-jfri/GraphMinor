module

public import GraphMinor.Wagner.K33Sub
public import GraphMinor.Wagner.TV8

/-!
# A cross link in a subdivision of `K_{3,3}` gives a subdivision of `V_8`

Let `S` be a subdivision of `K_{3,3}`. Suppose a path `Q` joins an inner vertex `x` of the path from
`a i` to `b k` and an inner vertex `y` of the path from `a j` to `b l`, where `i ≠ j` and `k ≠ l`,
and the inner vertices of `Q` avoid `S`. Then `S` together with `Q` is a subdivision of `V_8`
(`K33Sub.tv8_of_cross`).

After renaming we may take `(i, k) = (0, 0)` and `(j, l) = (1, 1)`. The eight-cycle of `V_8` is
`x, a 0, b 2, a 1, y, b 1, a 2, b 0`, and its four diagonals are `Q` and the paths `a 0 b 1`,
`b 2 a 2` and `a 1 b 0`.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

namespace K33Sub

theorem path_prefix {a x b : γ} {p₁ p₂ : List γ}
    (h : (a :: (p₁ ++ x :: p₂) ++ [b]).Nodup ∧ (a :: (p₁ ++ x :: p₂) ++ [b]).IsChain K.Adj) :
    (a :: p₁ ++ [x]).Nodup ∧ (a :: p₁ ++ [x]).IsChain K.Adj := by
  have e : a :: (p₁ ++ x :: p₂) ++ [b] = (a :: p₁ ++ [x]) ++ (p₂ ++ [b]) := by simp
  rw [e] at h
  exact ⟨h.1.sublist (List.sublist_append_left _ _), h.2.left_of_append⟩

theorem path_suffix {a x b : γ} {p₁ p₂ : List γ}
    (h : (a :: (p₁ ++ x :: p₂) ++ [b]).Nodup ∧ (a :: (p₁ ++ x :: p₂) ++ [b]).IsChain K.Adj) :
    (x :: p₂ ++ [b]).Nodup ∧ (x :: p₂ ++ [b]).IsChain K.Adj := by
  have e : a :: (p₁ ++ x :: p₂) ++ [b] = (a :: p₁) ++ (x :: p₂ ++ [b]) := by simp
  rw [e] at h
  exact ⟨h.1.sublist (List.sublist_append_right _ _), h.2.right_of_append⟩

theorem path_reverse {a b : γ} {m : List γ}
    (h : (a :: m ++ [b]).Nodup ∧ (a :: m ++ [b]).IsChain K.Adj) :
    (b :: m.reverse ++ [a]).Nodup ∧ (b :: m.reverse ++ [a]).IsChain K.Adj := by
  have e : b :: m.reverse ++ [a] = (a :: m ++ [b]).reverse := by simp
  exact ⟨by rw [e]; exact List.nodup_reverse.mpr h.1, isChain_reverse_path h.2⟩

/-- Where the inner vertices of the twelve paths of the subdivision of `V_8` lie in `S`. -/
def loc : Fin 12 → Fin 3 × Fin 3 :=
  ![(0, 0), (0, 2), (1, 2), (1, 1), (1, 1), (2, 1), (2, 0), (0, 0), (0, 0), (0, 1), (2, 2), (1, 0)]

theorem loc_eq : ∀ k k' : Fin 12, k ≠ k' → k ≠ 8 → k' ≠ 8 → loc k = loc k' →
    (k = 0 ∧ k' = 7) ∨ (k = 7 ∧ k' = 0) ∨ (k = 3 ∧ k' = 4) ∨ (k = 4 ∧ k' = 3) := by
  decide

theorem loc_00 : ∀ k : Fin 12, k ≠ 8 → loc k = (0, 0) → k = 0 ∨ k = 7 := by decide

theorem loc_11 : ∀ k : Fin 12, k ≠ 8 → loc k = (1, 1) → k = 3 ∨ k = 4 := by decide

variable (S : K33Sub K)

theorem m_ne_a {i j : Fin 3} {x : γ} (hx : x ∈ S.m i j) (i' : Fin 3) : x ≠ S.a i' :=
  S.m_a i j x hx i'

/-- **A cross link at `(0, 0)` and `(1, 1)` gives a subdivision of `V_8`.** -/
theorem tv8_00_11 {x y : γ} {mid : List γ} (hx : x ∈ S.m 0 0) (hy : y ∈ S.m 1 1)
    (hnd : (x :: mid ++ [y]).Nodup) (hch : (x :: mid ++ [y]).IsChain K.Adj)
    (hmid : ∀ z ∈ mid, ¬ S.InH z) : Nonempty (TV8 K) := by
  obtain ⟨p₁, p₂, hp⟩ := List.append_of_mem hx
  obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem hy
  have P00 := S.path 0 0
  rw [hp] at P00
  have P11 := S.path 1 1
  rw [hq] at P11
  have hnp : x ∉ p₁ ∧ x ∉ p₂ ∧ ∀ z ∈ p₁, z ∉ p₂ := by
    have h := (S.path 0 0).1
    rw [hp] at h
    have e : S.a 0 :: (p₁ ++ x :: p₂) ++ [S.b 0] = S.a 0 :: (p₁ ++ x :: (p₂ ++ [S.b 0])) := by
      simp
    rw [e, List.nodup_cons, List.nodup_append, List.nodup_cons] at h
    refine ⟨fun h' => h.2.2.2 x h' x List.mem_cons_self rfl,
      fun h' => h.2.2.1.1 (List.mem_append_left _ h'),
      fun z hz hz' => h.2.2.2 z hz z (List.mem_cons_of_mem _ (List.mem_append_left _ hz')) rfl⟩
  have hnq : y ∉ q₁ ∧ y ∉ q₂ ∧ ∀ z ∈ q₁, z ∉ q₂ := by
    have h := (S.path 1 1).1
    rw [hq] at h
    have e : S.a 1 :: (q₁ ++ y :: q₂) ++ [S.b 1] = S.a 1 :: (q₁ ++ y :: (q₂ ++ [S.b 1])) := by
      simp
    rw [e, List.nodup_cons, List.nodup_append, List.nodup_cons] at h
    refine ⟨fun h' => h.2.2.2 y h' y List.mem_cons_self rfl,
      fun h' => h.2.2.1.1 (List.mem_append_left _ h'),
      fun z hz hz' => h.2.2.2 z hz z (List.mem_cons_of_mem _ (List.mem_append_left _ hz')) rfl⟩
  have hp₁ : ∀ z ∈ p₁, z ∈ S.m 0 0 := fun z hz => by rw [hp]; exact List.mem_append_left _ hz
  have hp₂ : ∀ z ∈ p₂, z ∈ S.m 0 0 := fun z hz => by
    rw [hp]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hz)
  have hq₁ : ∀ z ∈ q₁, z ∈ S.m 1 1 := fun z hz => by rw [hq]; exact List.mem_append_left _ hz
  have hq₂ : ∀ z ∈ q₂, z ∈ S.m 1 1 := fun z hz => by
    rw [hq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hz)
  let w : Fin 8 → γ := ![x, S.a 0, S.b 2, S.a 1, y, S.b 1, S.a 2, S.b 0]
  let I : Fin 12 → List γ := ![p₁.reverse, S.m 0 2, (S.m 1 2).reverse, q₁, q₂, (S.m 2 1).reverse,
    S.m 2 0, p₂.reverse, mid, S.m 0 1, (S.m 2 2).reverse, S.m 1 0]
  -- Where the inner vertices lie.
  have hI : ∀ k z, z ∈ I k → (k = 8 ∧ z ∈ mid) ∨ (k ≠ 8 ∧ z ∈ S.m (loc k).1 (loc k).2 ∧
      (k = 0 → z ∈ p₁) ∧ (k = 7 → z ∈ p₂) ∧ (k = 3 → z ∈ q₁) ∧ (k = 4 → z ∈ q₂)) := by
    have nope : ∀ {P : Prop} {k k' : Fin 12}, k ≠ k' → k = k' → P := fun h e => absurd e h
    intro k z hz
    fin_cases k
    · have hz' : z ∈ p₁ := List.mem_reverse.mp hz
      exact Or.inr ⟨by decide, hp₁ z hz', fun _ => hz', nope (by decide), nope (by decide),
          nope (by decide)⟩
    · exact Or.inr ⟨by decide, hz, nope (by decide), nope (by decide), nope (by decide),
        nope (by decide)⟩
    · exact Or.inr ⟨by decide, List.mem_reverse.mp hz, nope (by decide), nope (by decide),
        nope (by decide), nope (by decide)⟩
    · exact Or.inr ⟨by decide, hq₁ z hz, nope (by decide), nope (by decide), fun _ => hz,
        nope (by decide)⟩
    · exact Or.inr ⟨by decide, hq₂ z hz, nope (by decide), nope (by decide), nope (by decide),
        fun _ => hz⟩
    · exact Or.inr ⟨by decide, List.mem_reverse.mp hz, nope (by decide), nope (by decide),
        nope (by decide), nope (by decide)⟩
    · exact Or.inr ⟨by decide, hz, nope (by decide), nope (by decide), nope (by decide),
        nope (by decide)⟩
    · have hz' : z ∈ p₂ := List.mem_reverse.mp hz
      exact Or.inr ⟨by decide, hp₂ z hz', nope (by decide), fun _ => hz', nope (by decide),
          nope (by decide)⟩
    · exact Or.inl ⟨rfl, hz⟩
    · exact Or.inr ⟨by decide, hz, nope (by decide), nope (by decide), nope (by decide),
        nope (by decide)⟩
    · exact Or.inr ⟨by decide, List.mem_reverse.mp hz, nope (by decide), nope (by decide),
        nope (by decide), nope (by decide)⟩
    · exact Or.inr ⟨by decide, hz, nope (by decide), nope (by decide), nope (by decide),
        nope (by decide)⟩
  have hxH : S.InH x := Or.inr (Or.inr ⟨0, 0, hx⟩)
  have hyH : S.InH y := Or.inr (Or.inr ⟨1, 1, hy⟩)
  have hwH : ∀ i, S.InH (w i) := by
    intro i
    fin_cases i
    · exact hxH
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr (Or.inl ⟨2, rfl⟩)
    · exact Or.inl ⟨1, rfl⟩
    · exact hyH
    · exact Or.inr (Or.inl ⟨1, rfl⟩)
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inr (Or.inl ⟨0, rfl⟩)
  have hxa : ∀ t, x ≠ S.a t := S.m_a 0 0 x hx
  have hxb : ∀ t, x ≠ S.b t := S.m_b 0 0 x hx
  have hya : ∀ t, y ≠ S.a t := S.m_a 1 1 y hy
  have hyb : ∀ t, y ≠ S.b t := S.m_b 1 1 y hy
  have hxy : x ≠ y := fun e => S.m_disj 0 0 1 1 (by decide) x hx (e ▸ hy)
  have haa : ∀ t t', t ≠ t' → S.a t ≠ S.a t' := fun t t' h e => h (S.a_inj e)
  have hbb : ∀ t t', t ≠ t' → S.b t ≠ S.b t' := fun t t' h e => h (S.b_inj e)
  refine ⟨⟨w, I, ?_, ?_, ?_, ?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp only [w] at h <;> first
      | rfl
      | exact absurd h hxy
      | exact absurd h.symm hxy
      | exact absurd h (hxa _)
      | exact absurd h.symm (hxa _)
      | exact absurd h (hxb _)
      | exact absurd h.symm (hxb _)
      | exact absurd h (hya _)
      | exact absurd h.symm (hya _)
      | exact absurd h (hyb _)
      | exact absurd h.symm (hyb _)
      | exact absurd h (S.ab _ _)
      | exact absurd h.symm (S.ab _ _)
      | exact absurd h (haa _ _ (by decide))
      | exact absurd h (hbb _ _ (by decide))
  · intro k
    fin_cases k
    · exact path_reverse (path_prefix P00)
    · exact S.path 0 2
    · exact path_reverse (S.path 1 2)
    · exact path_prefix P11
    · exact path_suffix P11
    · exact path_reverse (S.path 2 1)
    · exact S.path 2 0
    · exact path_reverse (path_suffix P00)
    · exact ⟨hnd, hch⟩
    · exact S.path 0 1
    · exact path_reverse (S.path 2 2)
    · exact S.path 1 0
  · intro k k' hkk z hz hz'
    rcases hI k z hz with ⟨rfl, hzm⟩ | ⟨hk8, hzk, h0, h7, h3, h4⟩
    · rcases hI _ z hz' with ⟨h8, -⟩ | ⟨-, hzk', -⟩
      · exact hkk h8.symm
      · exact hmid z hzm (Or.inr (Or.inr ⟨_, _, hzk'⟩))
    · rcases hI k' z hz' with ⟨-, hzm⟩ | ⟨hk8', hzk', h0', h7', h3', h4'⟩
      · exact hmid z hzm (Or.inr (Or.inr ⟨_, _, hzk⟩))
      · by_cases hl : loc k = loc k'
        · rcases loc_eq k k' hkk hk8 hk8' hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hnp.2.2 z (h0 rfl) (h7' rfl)
          · exact hnp.2.2 z (h0' rfl) (h7 rfl)
          · exact hnq.2.2 z (h3 rfl) (h4' rfl)
          · exact hnq.2.2 z (h3' rfl) (h4 rfl)
        · exact S.m_disj _ _ _ _ hl z hzk hzk'
  · intro k z hz i hzi
    rcases hI k z hz with ⟨-, hzm⟩ | ⟨hk8, hzk, h0, h7, h3, h4⟩
    · exact hmid z hzm (hzi ▸ hwH i)
    · have hz_a : ∀ t, z ≠ S.a t := S.m_a _ _ z hzk
      have hz_b : ∀ t, z ≠ S.b t := S.m_b _ _ z hzk
      have hzx : z ≠ x := by
        rintro rfl
        by_cases hl : loc k = (0, 0)
        · rcases loc_00 k hk8 hl with rfl | rfl
          · exact hnp.1 (h0 rfl)
          · exact hnp.2.1 (h7 rfl)
        · exact S.m_disj _ _ 0 0 hl z hzk hx
      have hzy : z ≠ y := by
        rintro rfl
        by_cases hl : loc k = (1, 1)
        · rcases loc_11 k hk8 hl with rfl | rfl
          · exact hnq.1 (h3 rfl)
          · exact hnq.2.1 (h4 rfl)
        · exact S.m_disj _ _ 1 1 hl z hzk hy
      fin_cases i
      · exact hzx hzi
      · exact hz_a 0 hzi
      · exact hz_b 2 hzi
      · exact hz_a 1 hzi
      · exact hzy hzi
      · exact hz_b 1 hzi
      · exact hz_a 2 hzi
      · exact hz_b 0 hzi

theorem exists_perm_01 : ∀ i j : Fin 3, i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by
  decide

theorem perm_inH (σ τ : Equiv.Perm (Fin 3)) (z : γ) : (S.perm σ τ).InH z ↔ S.InH z := by
  simp only [InH, perm, comp_apply]
  constructor
  · rintro (⟨i, h⟩ | ⟨j, h⟩ | ⟨i, j, h⟩)
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr (Or.inl ⟨_, h⟩)
    · exact Or.inr (Or.inr ⟨_, _, h⟩)
  · rintro (⟨i, h⟩ | ⟨j, h⟩ | ⟨i, j, h⟩)
    · exact Or.inl ⟨σ.symm i, by simpa using h⟩
    · exact Or.inr (Or.inl ⟨τ.symm j, by simpa using h⟩)
    · exact Or.inr (Or.inr ⟨σ.symm i, τ.symm j, by simpa using h⟩)

/-- **A cross link gives a subdivision of `V_8`.** A path between an inner vertex of the path from
`a i` to `b k` and an inner vertex of the path from `a j` to `b l`, where `i ≠ j` and `k ≠ l`, whose
inner vertices avoid `S`, gives a subdivision of `V_8`. -/
theorem tv8_of_cross {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) {x y : γ} {mid : List γ}
    (hx : x ∈ S.m i k) (hy : y ∈ S.m j l) (hnd : (x :: mid ++ [y]).Nodup)
    (hch : (x :: mid ++ [y]).IsChain K.Adj) (hmid : ∀ z ∈ mid, ¬ S.InH z) :
    Nonempty (TV8 K) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_01 i j hij
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm_01 k l hkl
  refine (S.perm σ τ).tv8_00_11 (x := x) (y := y) ?_ ?_ hnd hch
    fun z hz h => hmid z hz ((S.perm_inH σ τ z).mp h)
  · show x ∈ S.m (σ 0) (τ 0)
    rw [hσ0, hτ0]
    exact hx
  · show y ∈ S.m (σ 1) (τ 1)
    rw [hσ1, hτ1]
    exact hy

end K33Sub

end GraphMinor.Wagner
