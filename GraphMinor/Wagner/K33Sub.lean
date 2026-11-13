module

public import GraphMinor.Wagner.PlanarPart

/-!
# Subdivisions of `K_{3,3}` and the links around them

A subdivision of `K_{3,3}` (`K33Sub`) has branch vertices `a i` and `b j` and, for all `i, j`, a
path `a i :: m i j ++ [b j]` whose inner parts `m i j` are pairwise disjoint and avoid the branch
vertices. We get it from `HasK33Subdiv` (`K33Sub.nonempty_of_hasK33Subdiv`). We can rename the
branch vertices on each side (`K33Sub.perm`) and swap the two sides (`K33Sub.transpose`).

Let `X i` be `a i` together with the inner vertices of the three paths at `a i`. In an internally
`4`-connected graph, deleting `b 0, b 1, b 2` leaves the sets `X i` joined, perhaps after deleting
one more vertex. So some path joins two different sets `X i` and `X j`, and its inner vertices avoid
the subdivision (`K33Sub.exists_linkA`). By symmetry the same holds on the side of the `b j`
(`K33Sub.exists_linkB`).
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

/-- A subdivision of `K_{3,3}` in `K`. -/
structure K33Sub (K : SimpleGraph γ) where
  /-- The branch vertices on the first side. -/
  a : Fin 3 → γ
  /-- The branch vertices on the second side. -/
  b : Fin 3 → γ
  /-- The inner vertices of the path from `a i` to `b j`. -/
  m : Fin 3 → Fin 3 → List γ
  a_inj : Injective a
  b_inj : Injective b
  ab : ∀ i j, a i ≠ b j
  path : ∀ i j, (a i :: m i j ++ [b j]).Nodup ∧ (a i :: m i j ++ [b j]).IsChain K.Adj
  m_disj : ∀ i j i' j', (i, j) ≠ (i', j') → ∀ x ∈ m i j, x ∉ m i' j'
  m_a : ∀ i j x, x ∈ m i j → ∀ i', x ≠ a i'
  m_b : ∀ i j x, x ∈ m i j → ∀ j', x ≠ b j'

namespace K33Sub

theorem mem_path_iff {x a b : γ} {m : List γ} : x ∈ a :: m ++ [b] ↔ x = a ∨ x ∈ m ∨ x = b := by
  simp

/-- A subdivision of `K_{3,3}` in the sense of `HasK33Subdiv` gives a `K33Sub`. -/
theorem nonempty_of_hasK33Subdiv (h : HasK33Subdiv K) : Nonempty (K33Sub K) := by
  obtain ⟨a, b, L, ha, hb, hab, hpath, hends, hdisj⟩ := h
  choose m hm using hends
  have hP : ∀ i j, (a i :: m i j ++ [b j]).Nodup ∧ (a i :: m i j ++ [b j]).IsChain K.Adj := by
    intro i j
    rw [← hm i j]
    exact ⟨(hpath i j).1, (hpath i j).2.1⟩
  have hma : ∀ i j x, x ∈ m i j → x ≠ a i ∧ x ≠ b j := by
    intro i j x hx
    have hnd : (a i :: (m i j ++ [b j])).Nodup := (hP i j).1
    rw [List.nodup_cons, List.nodup_append] at hnd
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hnd.1 (List.mem_append_left _ hx)
    · rintro rfl
      exact hnd.2.2.2 _ hx _ (List.mem_singleton_self _) rfl
  have hmem : ∀ i j x, x ∈ m i j → x ∈ L i j := fun i j x hx => by
    rw [hm i j, mem_path_iff]
    exact Or.inr (Or.inl hx)
  refine ⟨⟨a, b, m, ha, hb, hab, hP, ?_, ?_, ?_⟩⟩
  · intro i j i' j' hne x hx hx'
    rcases hdisj i j i' j' hne x (hmem i j x hx) (hmem i' j' x hx') with ⟨-, h⟩ | ⟨-, h⟩
    · exact (hma i j x hx).1 h
    · exact (hma i j x hx).2 h
  · intro i j x hx i' hxa
    by_cases hi : i' = i
    · subst hi
      exact (hma i' j x hx).1 hxa
    · have hx' : x ∈ L i' j := by
        rw [hm i' j, mem_path_iff]
        exact Or.inl hxa
      rcases hdisj i j i' j (fun e => hi (Prod.mk.inj e).1.symm) x (hmem i j x hx) hx' with
        ⟨-, h⟩ | ⟨-, h⟩
      · exact (hma i j x hx).1 h
      · exact (hma i j x hx).2 h
  · intro i j x hx j' hxb
    by_cases hj : j' = j
    · subst hj
      exact (hma i j' x hx).2 hxb
    · have hx' : x ∈ L i j' := by
        rw [hm i j', mem_path_iff]
        exact Or.inr (Or.inr hxb)
      rcases hdisj i j i j' (fun e => hj (Prod.mk.inj e).2.symm) x (hmem i j x hx) hx' with
        ⟨-, h⟩ | ⟨-, h⟩
      · exact (hma i j x hx).1 h
      · exact (hma i j x hx).2 h

variable (S : K33Sub K)

/-- Rename the branch vertices on both sides. -/
def perm (σ τ : Equiv.Perm (Fin 3)) : K33Sub K where
  a := S.a ∘ σ
  b := S.b ∘ τ
  m i j := S.m (σ i) (τ j)
  a_inj := S.a_inj.comp σ.injective
  b_inj := S.b_inj.comp τ.injective
  ab _ _ := S.ab _ _
  path _ _ := S.path _ _
  m_disj i j i' j' h := S.m_disj _ _ _ _ fun e => h (by
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    rw [σ.injective e1, τ.injective e2])
  m_a _ _ x hx _ := S.m_a _ _ x hx _
  m_b _ _ x hx _ := S.m_b _ _ x hx _

/-- Swap the two sides. -/
def transpose : K33Sub K where
  a := S.b
  b := S.a
  m i j := (S.m j i).reverse
  a_inj := S.b_inj
  b_inj := S.a_inj
  ab i j := (S.ab j i).symm
  path i j := by
    have e : S.b i :: (S.m j i).reverse ++ [S.a j] = (S.a j :: S.m j i ++ [S.b i]).reverse := by
      simp
    refine ⟨?_, isChain_reverse_path (S.path j i).2⟩
    rw [e]
    exact List.nodup_reverse.mpr (S.path j i).1
  m_disj i j i' j' h x hx hx' := S.m_disj j i j' i' (fun e => h (by
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    rw [e1, e2])) x (List.mem_reverse.mp hx) (List.mem_reverse.mp hx')
  m_a i j x hx i' := S.m_b j i x (List.mem_reverse.mp hx) i'
  m_b i j x hx j' := S.m_a j i x (List.mem_reverse.mp hx) j'

/-- The branch vertex `a i` with the inner vertices of the three paths at `a i`. -/
def X (i : Fin 3) : Set γ := {x | x = S.a i ∨ ∃ k, x ∈ S.m i k}

/-- The branch vertex `b k` with the inner vertices of the three paths at `b k`. -/
def Y (k : Fin 3) : Set γ := {x | x = S.b k ∨ ∃ i, x ∈ S.m i k}

/-- The vertices of the subdivision. -/
def InH (x : γ) : Prop := (∃ i, x = S.a i) ∨ (∃ j, x = S.b j) ∨ ∃ i j, x ∈ S.m i j

theorem transpose_X (i : Fin 3) : S.transpose.X i = S.Y i := by
  ext x
  simp [X, Y, transpose]

theorem transpose_inH (x : γ) : S.transpose.InH x ↔ S.InH x := by
  simp only [InH, transpose, List.mem_reverse]
  constructor
  · rintro (h | h | ⟨i, j, h⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨j, i, h⟩)
  · rintro (h | h | ⟨i, j, h⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨j, i, h⟩)

theorem X_disj (i j : Fin 3) (hij : i ≠ j) : Disjoint (S.X i) (S.X j) := by
  refine disjoint_left.mpr fun x hx hx' => ?_
  rcases hx with rfl | ⟨k, hk⟩ <;> rcases hx' with h | ⟨k', hk'⟩
  · exact hij (S.a_inj h)
  · exact S.m_a j k' _ hk' i rfl
  · exact S.m_a i k x hk j h
  · exact S.m_disj i k j k' (fun e => hij (Prod.mk.inj e).1) x hk hk'

/-- Two of three distinct values differ from any given vertex. -/
theorem exists_two_ne {f : Fin 3 → γ} (hf : Injective f) (u : γ) :
    ∃ i j, i ≠ j ∧ f i ≠ u ∧ f j ≠ u := by
  by_cases h0 : f 0 = u
  · refine ⟨1, 2, by decide, fun h => ?_, fun h => ?_⟩
    · exact absurd (hf (h.trans h0.symm)) (by decide)
    · exact absurd (hf (h.trans h0.symm)) (by decide)
  · by_cases h1 : f 1 = u
    · exact ⟨0, 2, by decide, h0, fun h => absurd (hf (h.trans h1.symm)) (by decide)⟩
    · exact ⟨0, 1, by decide, h0, h1⟩

/-- A link between two of the sets `X i`, avoiding the subdivision inside. -/
def LinkA (S : K33Sub K) : Prop :=
  ∃ i j x y mid, i ≠ j ∧ x ∈ S.X i ∧ y ∈ S.X j ∧ (x :: mid ++ [y]).Nodup ∧
    (x :: mid ++ [y]).IsChain K.Adj ∧ ∀ z ∈ mid, ¬ S.InH z

/-- A preconnected set without the vertices `b k` and with two of the vertices `a i` gives a link
between two sets `X i`. -/
theorem linkA_of_pc {W : Set γ} (hW : (K.induce W).Preconnected) (hWb : ∀ y ∈ W, ∀ k, y ≠ S.b k)
    {i j : Fin 3} (hij : i ≠ j) (hi : S.a i ∈ W) (hj : S.a j ∈ W) : S.LinkA := by
  let A : Fin 3 → Set γ := fun t => S.X t ∩ W
  obtain ⟨i', j', x, y, mid, hij', hx, hy, hmid, hnd, hch⟩ :=
    exists_hpath hW A (fun t t' h => (S.X_disj t t' h).mono inter_subset_left inter_subset_left)
      (fun t => inter_subset_right) hij (x := S.a i) (y := S.a j) ⟨Or.inl rfl, hi⟩
      ⟨Or.inl rfl, hj⟩
  refine ⟨i', j', x, y, mid, hij', hx.1, hy.1, hnd, hch, fun z hz hzH => ?_⟩
  obtain ⟨hzW, hzA⟩ := hmid z hz
  rcases hzH with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, k, hzm⟩
  · exact hzA t ⟨Or.inl rfl, hzW⟩
  · exact hWb _ hzW t rfl
  · exact hzA t ⟨Or.inr ⟨k, hzm⟩, hzW⟩

end K33Sub

variable {N : ℕ} {K : SimpleGraph (Fin N)}

namespace K33Sub

/-- **Links on the first side.** In an internally `4`-connected graph, some path joins two
different sets `X i` and `X j`, and its inner vertices avoid the subdivision. -/
theorem exists_linkA (hi : IsInternally4ConnFin K) (S : K33Sub K) : S.LinkA := by
  have hcard : (range S.b).ncard = 3 := by
    rw [← image_univ, ncard_image_of_injective _ S.b_inj, ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rcases i4c_cut3 hi (range S.b) hcard with hpc | ⟨-, u, -, hpc⟩
  · refine S.linkA_of_pc hpc (fun y hy k e => hy ⟨k, e.symm⟩) (i := 0) (j := 1) (by decide)
      ?_ ?_
    · rintro ⟨k, hk⟩
      exact S.ab 0 k hk.symm
    · rintro ⟨k, hk⟩
      exact S.ab 1 k hk.symm
  · obtain ⟨i, j, hij, hiu, hju⟩ := exists_two_ne S.a_inj u
    refine S.linkA_of_pc hpc (fun y hy k e => hy.1 ⟨k, e.symm⟩) hij ⟨?_, hiu⟩ ⟨?_, hju⟩
    · rintro ⟨k, hk⟩
      exact S.ab i k hk.symm
    · rintro ⟨k, hk⟩
      exact S.ab j k hk.symm

/-- **Links on the second side.** In an internally `4`-connected graph, some path joins two
different sets `Y k` and `Y l`, and its inner vertices avoid the subdivision. -/
theorem exists_linkB (hi : IsInternally4ConnFin K) (S : K33Sub K) :
    ∃ k l x y mid, k ≠ l ∧ x ∈ S.Y k ∧ y ∈ S.Y l ∧ (x :: mid ++ [y]).Nodup ∧
      (x :: mid ++ [y]).IsChain K.Adj ∧ ∀ z ∈ mid, ¬ S.InH z := by
  obtain ⟨k, l, x, y, mid, hkl, hx, hy, hnd, hch, hmid⟩ := S.transpose.exists_linkA hi
  rw [transpose_X] at hx hy
  exact ⟨k, l, x, y, mid, hkl, hx, hy, hnd, hch, fun z hz h => hmid z hz
    ((S.transpose_inH z).mpr h)⟩

end K33Sub

end GraphMinor.Wagner
