module

public import GraphMinor.Compute.TwoPathsDriverSolve
public import GraphMinor.Compute.TwoPathsInst
public import GraphMinor.Compute.TwoPathsCount
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.Lemma43Tools

/-!
# The driver of Algorithm 5.1: the instances of a run

The proof of the driver follows the recursion of Algorithm 5.1 (Humeau and Pous, page 18), by
induction on the instances. This file proves what that induction needs about one split.

Each instance `(H, T)` of a run has a *vertex set* `S`: every edge of `H` has both ends in `S`
(`EdgesIn H S`). The first instance has `S` the set of all vertices. Subinstance `i` of a split has
the vertex set `S ∩ side i` (`childSet`). Then (`split_counts`):
* the cycle of each subinstance is a cycle of its graph (Proposition 5.1, through
  `isCycleList_sub`), and the vertex sets meet as in `TwoPathsCount.lean`, so the potential
  `2|S| - |T| - 3` drops by exactly one and `|S| - |T|` drops by exactly `|m|`;
* the graph of a subinstance has at most `|E(H)| + |F|/2` edges (`card_edgeFinset_sub_le`).

The answers combine as line 11 says (`not_isCrossed_of_sub`): if neither subinstance is crossed,
the instance is not crossed (Proposition 5.2 in the form `isCrossed_iff_sub`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {N : ℕ}

/-! ### Vertex sets -/

/-- Every edge of `H` has its ends in `S`. -/
def EdgesIn (H : SimpleGraph (Fin N)) (S : Finset (Fin N)) : Prop := ∀ u v, H.Adj u v → u ∈ S

/-- The vertices of a walk that starts in `S` lie in `S`, when every edge has its ends in `S`. -/
theorem support_subset_of_edgesIn {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    (hG : EdgesIn G S) {u v : Fin N} (W : G.Walk u v) (hu : u ∈ S) : ∀ x ∈ W.support, x ∈ S := by
  induction W with
  | nil => intro x hx; simp at hx; rw [hx]; exact hu
  | cons h p ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu
    · exact ih (hG _ _ h.symm) x hx

/-- A vertex of a cycle of `H` is the end of an edge, so it lies in `S`. -/
theorem mem_of_isCycleList {H : SimpleGraph (Fin N)} {S : Finset (Fin N)} (hS : EdgesIn H S)
    {T : List (Fin N)} (hT : IsCycleList H T) {x : Fin N} (hx : x ∈ T) : x ∈ S := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hl : i < (T.zip (T.rotate 1)).length := by simp; exact hi
  have := hT.2.2 _ (List.getElem_mem hl)
  rw [List.getElem_zip] at this
  exact hS _ _ this

theorem length_le_card_of_subset {S : Finset (Fin N)} {C : List (Fin N)} (hnd : C.Nodup)
    (hC : ∀ v ∈ C, v ∈ S) : C.length ≤ S.card := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card (fun v hv => hC v (List.mem_toFinset.mp hv))

/-- A vertex of `P'` that is on a side of `P'` in `H + F` is the end of an edge of `H`, when the
side misses `P'` and both ends of every edge of `F` lie on `P'`. The first edge of the path to the
side leaves `P'`, so it is not an edge of `F`. -/
theorem mem_of_isOnSide {H : SimpleGraph (Fin N)} {S : Finset (Fin N)} (hS : EdgesIn H S)
    {F : List ℕ} {Pv : List (Fin N)} (hF : IsNewEdgeList H Pv F) {X U : Set (Fin N)}
    (hX : ∀ x ∈ Pv, x ∈ X) (hU : ∀ x ∈ U, x ∉ Pv) {v : Fin N} (hv : v ∈ Pv)
    (h : IsOnSide (H ⊔ pairGraph N F) X U v) : v ∈ S := by
  obtain ⟨z, hz, p, -, hin⟩ := h
  cases p with
  | nil => exact absurd hv (hU _ hz)
  | @cons _ x _ hadj q =>
    have hx : x ∉ Pv := by
      by_cases hxz : x = z
      · exact hxz ▸ hU _ hz
      · exact fun hxP => hin x (by simp) (hadj.ne.symm) hxz (hX x hxP)
    rcases hadj with h | ⟨-, i, hi⟩
    · exact hS v x h
    · exfalso
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨u', v', -, e2, -, -, hv', -⟩ := hF.2.1 i (List.getElem?_eq_some_iff.mp h2).1
        rw [h2] at e2
        exact hx ((Fin.ext (Option.some.inj e2)) ▸ hv')
      · obtain ⟨u', v', e1, -, -, hu', -, -⟩ := hF.2.1 i (List.getElem?_eq_some_iff.mp h2).1
        rw [h1] at e1
        exact hx ((Fin.ext (Option.some.inj e1)) ▸ hu')

/-- The vertex set of an instance is also a vertex set of `H + F` after a completion: both ends of
each edge of `F` lie on `P'`, and every vertex of `P'` is on side `A`, so it is the end of an edge
of `H` (`mem_of_isOnSide`). -/
theorem edgesIn_sup_pair {H : SimpleGraph (Fin N)} {S : Finset (Fin N)} (hS : EdgesIn H S)
    {F : List ℕ} {a b : Fin N} {C A B : List (Fin N)} {P' : (H ⊔ pairGraph N F).Walk a b}
    (hF : IsNewEdgeList H P'.support F) (hA : ∀ v ∈ A, v ∉ P'.support)
    (hsides : OnBothSides (H ⊔ pairGraph N F) C A B P') :
    EdgesIn (H ⊔ pairGraph N F) S := by
  have hP : ∀ x ∈ P'.support, x ∈ S := fun x hx =>
    mem_of_isOnSide hS hF (fun _ h => Or.inr h) hA hx (hsides x hx).1
  intro u v h
  rcases h with h | ⟨-, i, hi⟩
  · exact hS u v h
  · rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨u', v', e1, -, -, hu', -, -⟩ := hF.2.1 i (List.getElem?_eq_some_iff.mp h2).1
      rw [h1] at e1
      have : u = u' := Fin.ext (Option.some.inj e1)
      exact this ▸ hP u' hu'
    · obtain ⟨u', v', -, e2, -, -, hv', -⟩ := hF.2.1 i (List.getElem?_eq_some_iff.mp h2).1
      rw [h2] at e2
      have : u = v' := Fin.ext (Option.some.inj e2)
      exact this ▸ hP v' hv'

/-- The side `i` of a split, as a set. -/
def sideSet (G : SimpleGraph (Fin N)) (Pv A : List (Fin N)) (i : ℕ) : Set (Fin N) :=
  if i = 1 then sideOne G Pv A else sideTwo G Pv A

theorem mem_sideSet_one {G : SimpleGraph (Fin N)} {Pv A : List (Fin N)} {x : Fin N} :
    x ∈ sideSet G Pv A 1 ↔ x ∈ Pv ∨ x ∈ reachOff G Pv A := by
  simp only [sideSet, if_pos rfl, sideOne]; rfl

theorem mem_sideSet_two {G : SimpleGraph (Fin N)} {Pv A : List (Fin N)} {x : Fin N} :
    x ∈ sideSet G Pv A 2 ↔ x ∈ Pv ∨ x ∉ reachOff G Pv A := by
  simp only [sideSet, show (2 : ℕ) ≠ 1 by decide, if_false, sideTwo]; rfl

theorem subGraph_eq (G : SimpleGraph (Fin N)) (Pv A : List (Fin N)) (i : ℕ) :
    subGraph G Pv A i = restrict G (sideSet G Pv A i) := by
  rcases i with _ | _ | i <;> simp [subGraph, sideSet]

/-- The vertex set of subinstance `i`. -/
noncomputable def childSet (S : Finset (Fin N)) (G : SimpleGraph (Fin N)) (Pv A : List (Fin N))
    (i : ℕ) : Finset (Fin N) :=
  by classical exact S.filter (· ∈ sideSet G Pv A i)

theorem mem_childSet {S : Finset (Fin N)} {G : SimpleGraph (Fin N)} {Pv A : List (Fin N)}
    {i : ℕ} {x : Fin N} : x ∈ childSet S G Pv A i ↔ x ∈ S ∧ x ∈ sideSet G Pv A i := by
  classical
  simp [childSet]

theorem edgesIn_sub {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} (hS : EdgesIn G S)
    (Pv A : List (Fin N)) (i : ℕ) : EdgesIn (subGraph G Pv A i) (childSet S G Pv A i) := by
  intro u v h
  rw [subGraph_eq] at h
  exact mem_childSet.mpr ⟨hS u v h.1, h.2.1⟩

/-! ### Edges -/

/-- The graph of a flat list of pairs has at most half as many edges as the list has entries. -/
theorem card_edgeFinset_pairGraph_le (F : List ℕ) [Fintype (pairGraph N F).edgeSet] :
    (pairGraph N F).edgeFinset.card ≤ F.length / 2 := by
  classical
  let key : Sym2 (Fin N) → ℕ := fun e =>
    if h : ∃ i, ∃ u v : Fin N, e = s(u, v) ∧ F[2 * i]? = some u.1 ∧ F[2 * i + 1]? = some v.1
    then h.choose else 0
  have hkey : ∀ e ∈ (pairGraph N F).edgeFinset, ∃ u v : Fin N, e = s(u, v) ∧
      F[2 * key e]? = some u.1 ∧ F[2 * key e + 1]? = some v.1 := by
    intro e he
    have hex : ∃ i, ∃ u v : Fin N, e = s(u, v) ∧ F[2 * i]? = some u.1 ∧
        F[2 * i + 1]? = some v.1 := by
      induction e using Sym2.ind with
      | _ x y =>
        rw [mem_edgeFinset, mem_edgeSet] at he
        obtain ⟨-, i, hi⟩ := he
        rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨i, x, y, rfl, h1, h2⟩
        · exact ⟨i, y, x, Sym2.eq_swap, h1, h2⟩
    have hk : key e = hex.choose := dif_pos hex
    rw [hk]
    exact hex.choose_spec
  have hcard := Finset.card_le_card_of_injOn key (s := (pairGraph N F).edgeFinset)
    (t := Finset.range (F.length / 2)) (fun e he => by
      obtain ⟨u, v, -, -, h2⟩ := hkey e he
      have := (List.getElem?_eq_some_iff.mp h2).1
      simp only [Finset.coe_range, Set.mem_Iio]; omega)
    (fun e he e' he' heq => by
      obtain ⟨u, v, rfl, h1, h2⟩ := hkey e he
      obtain ⟨u', v', rfl, h1', h2'⟩ := hkey e' he'
      rw [heq, h1'] at h1
      rw [heq, h2'] at h2
      rw [Fin.ext (Option.some.inj h1), Fin.ext (Option.some.inj h2)])
  simpa using hcard

/-- **Edges of a subinstance.** The graph of a subinstance of `H + F` has at most
`|E(H)| + |F|/2` edges. -/
theorem card_edgeFinset_sub_le (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (F : List ℕ)
    (Pv A : List (Fin N)) (i : ℕ) [Fintype (subGraph (H ⊔ pairGraph N F) Pv A i).edgeSet] :
    (subGraph (H ⊔ pairGraph N F) Pv A i).edgeFinset.card ≤ H.edgeFinset.card + F.length / 2 := by
  classical
  calc (subGraph (H ⊔ pairGraph N F) Pv A i).edgeFinset.card
      ≤ (H ⊔ pairGraph N F).edgeFinset.card :=
        Finset.card_le_card (edgeFinset_subset_edgeFinset.mpr (subGraph_le _ _ _ _))
    _ = (H.edgeFinset ∪ (pairGraph N F).edgeFinset).card := by rw [edgeFinset_sup]
    _ ≤ H.edgeFinset.card + (pairGraph N F).edgeFinset.card := Finset.card_union_le _ _
    _ ≤ H.edgeFinset.card + F.length / 2 := by
        have := card_edgeFinset_pairGraph_le (N := N) F
        omega

/-! ### Rotations -/

/-- A crossed tuple stays crossed after a rotation. -/
theorem isCrossed_rotate {V : Type*} {G : SimpleGraph V} {T : List V} (h : IsCrossed G T)
    (k : ℕ) : IsCrossed G (T.rotate k) := by
  rcases Nat.eq_zero_or_pos T.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0] at h ⊢; simpa using h
  apply IsCrossed.of_rotate (T.length - k % T.length)
  rw [List.rotate_rotate, ← List.rotate_mod]
  have hk := Nat.mod_lt k hpos
  have : (k + (T.length - k % T.length)) % T.length = 0 := by
    rw [show k + (T.length - k % T.length) = T.length * (k / T.length + 1) by
      have := Nat.div_add_mod k T.length
      rw [Nat.mul_add, Nat.mul_one]; omega]
    exact Nat.mul_mod_right _ _
  rw [this, List.rotate_zero]; exact h

/-! ### One split -/

section Split

variable {w : ℕ} {comp : Cmd} {c : ℕ} {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
  {lists : Fin N → List ℕ} {T : List (Fin N)} {s₁ : State} {a b : Fin N} {A B m : List (Fin N)}
  {P : H.Walk a b} {F : List ℕ} {P' : (H ⊔ pairGraph N F).Walk a b}

/-- **Line 11, the answer `False`.** If neither subinstance is crossed, `T` is not crossed. -/
theorem not_isCrossed_of_sub (hd : SplitData w comp c H lists T s₁ a b A B m P F P')
    (h₁ : ¬ IsCrossed (subGraph (H ⊔ pairGraph N F) P'.support A 1) (subCycle a b A B m 1))
    (h₂ : ¬ IsCrossed (subGraph (H ⊔ pairGraph N F) P'.support A 2) (subCycle a b A B m 2)) :
    ¬ IsCrossed H T := by
  intro h
  have h' := isCrossed_rotate h (T.idxOf a)
  rw [hd.rot] at h'
  rcases (isCrossed_iff_sub hd.split.cyc hd.split.neA hd.split.neB hd.safe hd.tpath hd.supp
    hd.sides hd.sep).mp h' with h | h
  · exact h₁ h
  · exact h₂ h

/-- The cycle of subinstance `i` is a cycle of its graph. -/
theorem SplitData.childCycle (hd : SplitData w comp c H lists T s₁ a b A B m P F P') (i : ℕ)
    (hi : i = 1 ∨ i = 2) :
    IsCycleList (subGraph (H ⊔ pairGraph N F) P'.support A i) (subCycle a b A B m i) := by
  have h := isCycleList_sub hd.split.cyc hd.split.neA hd.split.neB hd.tpath hd.supp hd.sep
  rcases hi with rfl | rfl
  · exact h.1
  · exact h.2

/-- **The counts of one split.** With `S` the vertex set of the instance, the vertex sets of the
subinstances satisfy: the potential `2|S| - |T| - 3` drops by exactly one, `|S| - |T|` drops by
exactly `|m|`, and each subinstance has at most `|E(H)| + |m| + 1` edges. -/
theorem SplitData.counts (hd : SplitData w comp c H lists T s₁ a b A B m P F P')
    {S : Finset (Fin N)} (hS : EdgesIn H S) (hT : IsCycleList H T) :
    let G := H ⊔ pairGraph N F
    let S₁ := childSet S G P'.support A 1
    let S₂ := childSet S G P'.support A 2
    (2 * S₁.card - (subCycle a b A B m 1).length - 3) +
        (2 * S₂.card - (subCycle a b A B m 2).length - 3) + 1 = 2 * S.card - T.length - 3 ∧
      (S₁.card - (subCycle a b A B m 1).length) + (S₂.card - (subCycle a b A B m 2).length) +
        m.length = S.card - T.length ∧
      EdgesIn (subGraph G P'.support A 1) S₁ ∧ EdgesIn (subGraph G P'.support A 2) S₂ ∧
      F.length / 2 ≤ m.length + 1 := by
  intro G S₁ S₂
  have hTl : T.length = (a :: A ++ b :: B).length := by rw [← hd.rot, List.length_rotate]
  have haS : a ∈ S := mem_of_isCycleList hS hT (by
    have : a ∈ T.rotate (T.idxOf a) := by rw [hd.rot]; simp
    exact List.mem_rotate.mp this)
  have hG : EdgesIn G S := edgesIn_sup_pair hS hd.newEdges hd.notMem_A hd.sides
  have hPS := support_subset_of_edgesIn hG P' haS
  have hnd : (a :: m ++ [b]).Nodup := hd.supp ▸ hd.tpath.1.support_nodup
  have hU : S₁ ∪ S₂ = S := by
    ext x
    simp only [Finset.mem_union, S₁, S₂, mem_childSet, mem_sideSet_one, mem_sideSet_two]
    tauto
  have hI : S₁ ∩ S₂ = (a :: m ++ [b]).toFinset := by
    ext x
    simp only [Finset.mem_inter, S₁, S₂, mem_childSet, mem_sideSet_one, mem_sideSet_two,
      List.mem_toFinset]
    rw [← hd.supp]
    constructor
    · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩; tauto
    · intro h; exact ⟨⟨hPS x h, Or.inl h⟩, ⟨hPS x h, Or.inl h⟩⟩
  have hE₁ := edgesIn_sub hG P'.support A 1
  have hE₂ := edgesIn_sub hG P'.support A 2
  have hC₁ := hd.childCycle 1 (Or.inl rfl)
  have hC₂ := hd.childCycle 2 (Or.inr rfl)
  have hl₁ := length_add_three_le hC₁.2.1 hC₁.1 (fun v hv => mem_of_isCycleList hE₁ hC₁ hv)
  have hl₂ := length_add_three_le hC₂.2.1 hC₂.1 (fun v hv => mem_of_isCycleList hE₂ hC₂ hv)
  have hpot := potential_split hnd hU hI hl₁ hl₂
  have hoff := offCycle_split hnd hU hI
    (length_le_card_of_subset hC₁.2.1 (fun v hv => mem_of_isCycleList hE₁ hC₁ hv))
    (length_le_card_of_subset hC₂.2.1 (fun v hv => mem_of_isCycleList hE₂ hC₂ hv))
  refine ⟨by rw [hTl]; exact hpot, by rw [hTl]; exact hoff, hE₁, hE₂, ?_⟩
  have := hd.lenF
  rw [hd.supp] at this
  simp at this
  omega

end Split

end GraphMinor.Compute.TwoPaths
