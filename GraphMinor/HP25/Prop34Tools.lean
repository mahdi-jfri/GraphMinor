module

public import GraphMinor.HP25.WebSplit
public import GraphMinor.HP25.Lemma33
import GraphMinor.HP25.Prop23
import GraphMinor.HP25.RibEdges
import GraphMinor.HP25.RibConnected

/-!
# Tools for Proposition 3.4

* Cycle edges in terms of positions on the cycle (`isCycleEdge_iff_idxOf`), and the rotation that
  brings two vertices of a cycle to the front (`exists_rotate_cons_cons`).
* Walk surgery (`reach_side`): when every edge of `G` lies inside `S₁` or inside `S₂`, the two sets
  meet in `{c, c'}` and `cc'` is an edge, a walk between two vertices of `S₁` gives one inside `S₁`
  on the vertices of the walk. Each excursion into `S₂` leaves and comes back through `c` or `c'`,
  and is replaced by nothing or by the edge `cc'`.
* Ribs without chords (`IsRibOn.reachable_inner`): when no two non-consecutive vertices of the frame
  are adjacent, and the frame has at least four vertices, the inner vertices of the rib are
  connected through inner vertices. The proof goes around the frame with the fans of
  Proposition 2.3.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

/-! ### Cycle edges and positions -/

/-- A cycle edge joins two vertices whose positions on the cycle differ by one, cyclically. -/
theorem isCycleEdge_iff_idxOf [DecidableEq V] {C : List V} (hnd : C.Nodup) {u v : V} :
    IsCycleEdge C u v ↔ u ∈ C ∧ v ∈ C ∧ (C.idxOf v = (C.idxOf u + 1) % C.length ∨
      C.idxOf u = (C.idxOf v + 1) % C.length) := by
  have hpos : ∀ i (hi : i < C.length), C.idxOf C[i] = i := fun i hi => hnd.idxOf_getElem _ _
  constructor
  · rintro ⟨p, hp, he⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hi1 : i < C.length := by simp at hi; omega
    have hn : 0 < C.length := by omega
    have e : (C.zip (C.rotate 1))[i] = (C[i], C[(i + 1) % C.length]'(Nat.mod_lt _ hn)) := by
      simp [List.getElem_zip, List.getElem_rotate]
    rw [e] at he
    have h1 := hpos i hi1
    have h2 := hpos ((i + 1) % C.length) (Nat.mod_lt _ hn)
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨List.getElem_mem _, List.getElem_mem _, Or.inl (by rw [h1, h2])⟩
    · exact ⟨List.getElem_mem _, List.getElem_mem _, Or.inr (by rw [h1, h2])⟩
  · rintro ⟨hu, hv, h | h⟩
    · have hn : 0 < C.length := List.length_pos_of_mem hu
      have hiu := List.idxOf_lt_length_of_mem hu
      have hi : C.idxOf u < (C.zip (C.rotate 1)).length := by simp [hiu]
      refine ⟨_, List.getElem_mem hi, ?_⟩
      simp only [List.getElem_zip, List.getElem_rotate]
      rw [List.getElem_idxOf hiu]
      congr 1
      conv_lhs => rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)]
      simp only [h]
    · have hn : 0 < C.length := List.length_pos_of_mem hu
      have hiv := List.idxOf_lt_length_of_mem hv
      have hi : C.idxOf v < (C.zip (C.rotate 1)).length := by simp [hiv]
      refine ⟨_, List.getElem_mem hi, ?_⟩
      simp only [List.getElem_zip, List.getElem_rotate]
      rw [List.getElem_idxOf hiv, Sym2.eq_swap]
      congr 1
      conv_lhs => rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hu)]
      simp only [h]

/-- Positions in the list `a :: A ++ b :: B`. -/
theorem idxOf_cons_append_cons [DecidableEq V] {a b : V} {A B : List V}
    (hnd : (a :: A ++ b :: B).Nodup) :
    (a :: A ++ b :: B).idxOf a = 0 ∧ (a :: A ++ b :: B).idxOf b = A.length + 1 ∧
      (∀ v ∈ A, (a :: A ++ b :: B).idxOf v = A.idxOf v + 1 ∧ A.idxOf v < A.length) ∧
      (a :: A ++ b :: B).length = A.length + B.length + 2 := by
  rw [List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons] at hnd
  have hab : b ≠ a := fun h => hnd.1 (List.mem_append_right _ (h ▸ List.mem_cons_self))
  have hbA : b ∉ A := fun h => hnd.2.2.2 b h b List.mem_cons_self rfl
  refine ⟨by simp, ?_, fun v hv => ?_, by simp; omega⟩
  · rw [List.cons_append, List.idxOf_cons_ne _ (Ne.symm hab), List.idxOf_append_of_notMem hbA]
    simp
  · have hva : v ≠ a := fun h => hnd.1 (List.mem_append_left _ (h ▸ hv))
    rw [List.cons_append, List.idxOf_cons_ne _ (Ne.symm hva), List.idxOf_append_of_mem hv]
    exact ⟨rfl, List.idxOf_lt_length_of_mem hv⟩

/-- In a cycle `a A b B`, `a` and `b` are consecutive exactly when `A` or `B` is empty. -/
theorem isCycleEdge_cons_append_cons_iff {a b : V} {A B : List V}
    (hnd : (a :: A ++ b :: B).Nodup) :
    IsCycleEdge (a :: A ++ b :: B) a b ↔ A = [] ∨ B = [] := by
  classical
  obtain ⟨ha, hb, -, hlen⟩ := idxOf_cons_append_cons hnd
  rw [isCycleEdge_iff_idxOf hnd, ha, hb, hlen]
  constructor
  · rintro ⟨-, -, h | h⟩
    · rw [Nat.mod_eq_of_lt (by omega)] at h
      left
      exact List.eq_nil_of_length_eq_zero (by omega)
    · by_cases hB : B = []
      · exact Or.inr hB
      · have := List.length_pos_of_ne_nil hB
        rw [Nat.mod_eq_of_lt (by omega)] at h
        omega
  · rintro (rfl | rfl)
    · exact ⟨by simp, by simp, Or.inl (by simp)⟩
    · refine ⟨by simp, by simp, Or.inr ?_⟩
      simp

/-- Two distinct vertices of a list come first and in between after a rotation. -/
theorem exists_rotate_cons_cons {C : List V} {c c' : V} (hc : c ∈ C) (hc' : c' ∈ C)
    (hne : c ≠ c') : ∃ k A B, C.rotate k = c :: A ++ c' :: B := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hc
  have hrot : (l₁ ++ c :: l₂).rotate l₁.length = c :: (l₂ ++ l₁) :=
    List.rotate_append_length_eq l₁ (c :: l₂) |>.trans (by simp)
  have hmem : c' ∈ l₂ ++ l₁ := by
    rcases List.mem_append.mp hc' with h | h
    · exact List.mem_append_right _ h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h.symm hne
      · exact List.mem_append_left _ h
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hmem
  exact ⟨l₁.length, A, B, by rw [hrot, hAB]; simp⟩

/-! ### Reachability along lists and walks -/

/-- The entries of a chain of `G` inside `X` are connected inside `X`. -/
theorem chain_reach {X : Set V} : ∀ {l : List V}, l.IsChain G.Adj → (∀ v ∈ l, v ∈ X) →
    ∀ u ∈ l, ∀ v ∈ l, (restrict G X).Reachable u v := by
  have key : ∀ {a : V} {l : List V}, (a :: l).IsChain G.Adj → (∀ v ∈ a :: l, v ∈ X) →
      ∀ v ∈ a :: l, (restrict G X).Reachable a v := by
    intro a l
    induction l generalizing a with
    | nil =>
      intro _ _ v hv
      rw [List.mem_singleton.mp hv]
    | cons b l ih =>
      intro hch hX v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rfl
      · have hab := (List.isChain_cons_cons.mp hch).1
        exact (Adj.reachable (G := restrict G X) ⟨hab, hX a (by simp), hX b (by simp)⟩).trans
          (ih (List.isChain_cons_cons.mp hch).2 (fun w hw => hX w (List.mem_cons_of_mem _ hw)) v hv)
  intro l hch hX u hu v hv
  cases l with
  | nil => simp at hu
  | cons a l => exact (key hch hX u hu).symm.trans (key hch hX v hv)

/-- **Walk surgery.** Every edge of `G` between `S₁` and `S₂` has an end in both, the two sets meet
in `{c, c'}` and `cc'` is an edge. A walk inside `M` that ends in `S₁` and starts in `S₁` gives a
walk inside `S₁ ∩ M` with the same ends. A walk that starts in `S₂ \ S₁` passes first through a
vertex `e ∈ {c, c'}` that reaches the end inside `S₁ ∩ M`. -/
theorem reach_side {S₁ S₂ M : Set V} {c c' : V}
    (hX : ∀ u ∈ S₁, ∀ v ∈ S₂, G.Adj u v → u ∈ S₂ ∨ v ∈ S₁)
    (hI : ∀ v, v ∈ S₁ → v ∈ S₂ → v = c ∨ v = c') (hcc : G.Adj c c') (hc : c ∈ S₁)
    (hc' : c' ∈ S₁) :
    ∀ {u z : V} (p : G.Walk u z), z ∈ S₁ → (∀ v ∈ p.support, v ∈ S₁ ∪ S₂) →
      (∀ v ∈ p.support, v ∈ M) →
      (u ∈ S₁ → (restrict G (S₁ ∩ M)).Reachable u z) ∧
      (u ∉ S₁ → ∃ e ∈ p.support, (e = c ∨ e = c') ∧ (restrict G (S₁ ∩ M)).Reachable e z)
  | _, _, .nil, hz, _, hM => ⟨fun _ => Reachable.refl _, fun hu => absurd hz hu⟩
  | u, z, .cons (v := y) huy q, hz, hS, hM => by
    have hS' : ∀ v ∈ q.support, v ∈ S₁ ∪ S₂ := fun v hv => hS v (by simp [hv])
    have hM' : ∀ v ∈ q.support, v ∈ M := fun v hv => hM v (by simp [hv])
    obtain ⟨ih1, ih2⟩ := reach_side hX hI hcc hc hc' q hz hS' hM'
    have huM : u ∈ M := hM u (by simp)
    have hyM : y ∈ M := hM' y (Walk.start_mem_support q)
    have hyS : y ∈ S₁ ∪ S₂ := hS' y (Walk.start_mem_support q)
    have huS : u ∈ S₁ ∪ S₂ := hS u (by simp)
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · by_cases hy : y ∈ S₁
      · exact (Adj.reachable (G := restrict G (S₁ ∩ M)) ⟨huy, ⟨hu, huM⟩, ⟨hy, hyM⟩⟩).trans (ih1 hy)
      · -- the walk leaves `S₁` at `u ∈ {c, c'}`
        have hyS₂ : y ∈ S₂ := hyS.resolve_left hy
        have hu2 : u ∈ S₂ := (hX u hu y hyS₂ huy).resolve_right hy
        obtain ⟨e, heq, he, hez⟩ := ih2 hy
        refine Reachable.trans ?_ hez
        have heS : e ∈ S₁ := by rcases he with rfl | rfl <;> assumption
        have heM : e ∈ M := hM' e heq
        by_cases hue : u = e
        · rw [hue]
        · have hadj : G.Adj u e := by
            rcases hI u hu hu2 with rfl | rfl <;> rcases he with rfl | rfl
            · exact absurd rfl hue
            · exact hcc
            · exact hcc.symm
            · exact absurd rfl hue
          exact Adj.reachable (G := restrict G (S₁ ∩ M)) ⟨hadj, ⟨hu, huM⟩, ⟨heS, heM⟩⟩
    · have hu2 : u ∈ S₂ := huS.resolve_left hu
      by_cases hy : y ∈ S₁
      · have hy2 : y ∈ S₂ := (hX y hy u hu2 huy.symm).resolve_right hu
        exact ⟨y, by simp, hI y hy hy2, ih1 hy⟩
      · obtain ⟨e, heq, he, hez⟩ := ih2 hy
        exact ⟨e, by simp [heq], he, hez⟩

/-- A vertex of a walk other than its ends lies strictly inside the list of its vertices. -/
theorem mem_tail_dropLast_support {s t u : V} (p : G.Walk s t) (hu : u ∈ p.support)
    (hus : u ≠ s) (hut : u ≠ t) : u ∈ p.support.tail.dropLast := by
  have h1 : u ∈ p.support.tail := by
    rw [← Walk.cons_tail_support p] at hu
    rcases List.mem_cons.mp hu with h | h
    · exact absurd h hus
    · exact h
  have hne : p.support.tail ≠ [] := List.ne_nil_of_mem h1
  have hlast : p.support.tail.getLast hne = t := by
    rw [List.getLast_tail]
    exact Walk.getLast_support p
  rw [← List.dropLast_append_getLast hne, hlast] at h1
  rcases List.mem_append.mp h1 with h | h
  · exact h
  · exact absurd (List.mem_singleton.mp h) hut

/-- The vertices of a path other than its ends, when they lie in `X`, are connected inside `X`. -/
theorem reach_interior {X : Set V} {s t : V} {p : G.Walk s t} (hp : p.IsPath)
    (hX : ∀ v ∈ p.support, v ≠ s → v ≠ t → v ∈ X) {u v : V} (hu : u ∈ p.support) (hus : u ≠ s)
    (hut : u ≠ t) (hv : v ∈ p.support) (hvs : v ≠ s) (hvt : v ≠ t) :
    (restrict G X).Reachable u v := by
  have hch : p.support.tail.dropLast.IsChain G.Adj := p.isChain_adj_support.tail.dropLast
  have hnd := hp.support_nodup
  rw [← Walk.cons_tail_support p, List.nodup_cons] at hnd
  have hne : p.support.tail ≠ [] := List.ne_nil_of_mem (mem_tail_dropLast_support p hu hus hut |>
    List.dropLast_subset _)
  have hlast : p.support.tail.getLast hne = t := by
    rw [List.getLast_tail]
    exact Walk.getLast_support p
  have hmem : ∀ w ∈ p.support.tail.dropLast, w ∈ X := by
    intro w hw
    have hw1 : w ∈ p.support.tail := List.dropLast_subset _ hw
    refine hX w (List.mem_of_mem_tail hw1) (fun h => hnd.1 (h ▸ hw1)) (fun h => ?_)
    have hnd2 := hnd.2
    rw [← List.dropLast_append_getLast hne, hlast, List.nodup_append] at hnd2
    exact hnd2.2.2 w hw t (by simp) h
  exact chain_reach hch hmem u (mem_tail_dropLast_support p hu hus hut) v
    (mem_tail_dropLast_support p hv hvs hvt)

/-! ### Ribs without chords -/

/-- The `i`-th and `(i+1)`-th vertices of a cycle are consecutive on it. -/
theorem isCycleEdge_getElem {C : List V} (hnd : C.Nodup) {i : ℕ} (hi : i + 1 < C.length) :
    IsCycleEdge C C[i] C[i + 1] := by
  classical
  rw [isCycleEdge_iff_idxOf hnd, hnd.idxOf_getElem, hnd.idxOf_getElem, Nat.mod_eq_of_lt hi]
  exact ⟨List.getElem_mem _, List.getElem_mem _, Or.inl rfl⟩

variable {R : Set V} {C : List V}

/-- In a rib without chords whose frame has at least four vertices, every frame vertex has a
neighbour off the frame, two consecutive frame vertices have a common neighbour off the frame, and
the inner neighbours of a frame vertex are connected through vertices off the frame. -/
theorem IsRibOn.no_chord_local (h : IsRibOn G R C) (h4 : 4 ≤ C.length)
    (hnc : ∀ u ∈ C, ∀ v ∈ C, G.Adj u v → IsCycleEdge C u v) :
    (∀ c d, IsCycleEdge C c d → ∃ w, (w ∈ R ∧ w ∉ C) ∧ G.Adj c w ∧ G.Adj d w) ∧
    (∀ c ∈ C, ∀ u v, (u ∈ R ∧ u ∉ C) → G.Adj c u → (v ∈ R ∧ v ∉ C) → G.Adj c v →
      (restrict G {w | w ∈ R ∧ w ∉ C}).Reachable u v) := by
  have hrib := h
  obtain ⟨hC, hR, φ, hφ⟩ := h
  refine ⟨fun c d hcd => ?_, fun c hc u v hu hcu hv hcv => ?_⟩
  · obtain ⟨w, hwR, hcw, hdw⟩ := ((hφ.common_neighbours hC hR (hR c hcd.mem_left)
      (hR d hcd.symm.mem_left) (hcd.adj hC)).2.1 hcd).2
    refine ⟨w, ⟨hwR, fun hwC => ?_⟩, hcw, hdw⟩
    have h1 := hnc c hcd.mem_left w hwC hcw
    have h2 := hnc d hcd.symm.mem_left w hwC hdw
    exact hC.not_isCycleEdge_frame_neighbours h4 hdw.ne hcd h1 h2
  · obtain ⟨d, d', hne, hd, hd', hall⟩ := hC.frame_neighbours hc
    obtain ⟨p, hp, hsupp, -⟩ := hrib.fan hne hd hd'
    have hdC : d ∈ C := hd.symm.mem_left
    have hd'C : d' ∈ C := hd'.symm.mem_left
    have hX : ∀ w ∈ p.support, w ≠ d → w ≠ d' → w ∈ {w | w ∈ R ∧ w ∉ C} := by
      intro w hw h1 h2
      obtain ⟨hwR, hcw⟩ := (hsupp w).mp hw
      refine ⟨hwR, fun hwC => ?_⟩
      rcases hall w (hnc c hc w hwC hcw) with rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
    exact reach_interior hp hX ((hsupp u).mpr ⟨hu.1, hcu⟩) (fun h => hu.2 (h ▸ hdC))
      (fun h => hu.2 (h ▸ hd'C)) ((hsupp v).mpr ⟨hv.1, hcv⟩) (fun h => hv.2 (h ▸ hdC))
      (fun h => hv.2 (h ▸ hd'C))

/-- **Ribs without chords.** In a rib whose frame has at least four vertices and no chord, every
frame vertex has a neighbour off the frame, and the vertices off the frame are connected through
vertices off the frame. -/
theorem IsRibOn.no_chord (h : IsRibOn G R C) (h4 : 4 ≤ C.length)
    (hnc : ∀ u ∈ C, ∀ v ∈ C, G.Adj u v → IsCycleEdge C u v) :
    (∀ c ∈ C, ∃ w, (w ∈ R ∧ w ∉ C) ∧ G.Adj c w) ∧
    ∀ u v, (u ∈ R ∧ u ∉ C) → (v ∈ R ∧ v ∉ C) →
      (restrict G {w | w ∈ R ∧ w ∉ C}).Reachable u v := by
  obtain ⟨hcom, hfan⟩ := h.no_chord_local h4 hnc
  have hrib := h
  obtain ⟨hC, hR, φ, hφ⟩ := h
  set I := {w | w ∈ R ∧ w ∉ C} with hI
  have hnd := hC.2.1
  have hn : 0 < C.length := by omega
  -- every frame vertex has an inner neighbour
  have hnbr : ∀ c ∈ C, ∃ w, (w ∈ R ∧ w ∉ C) ∧ G.Adj c w := by
    intro c hc
    obtain ⟨d, -, -, hd, -, -⟩ := hC.frame_neighbours hc
    obtain ⟨w, hw, hcw, -⟩ := hcom c d hd
    exact ⟨w, hw, hcw⟩
  refine ⟨hnbr, ?_⟩
  obtain ⟨w₀, hw₀, hcw₀⟩ := hnbr C[0] (List.getElem_mem hn)
  -- going around the frame, the inner neighbours of each frame vertex reach `w₀`
  have hring : ∀ i (hi : i < C.length), ∀ u, (u ∈ R ∧ u ∉ C) → G.Adj C[i] u →
      (restrict G I).Reachable w₀ u := by
    intro i
    induction i with
    | zero => exact fun hi u hu hcu => hfan C[0] (List.getElem_mem hn) w₀ u hw₀ hcw₀ hu hcu
    | succ i ih =>
      intro hi u hu hcu
      obtain ⟨w, hw, h1, h2⟩ := hcom _ _ (isCycleEdge_getElem hnd hi)
      exact (ih (by omega) w hw h1).trans (hfan _ (List.getElem_mem hi) w u hw h2 hu hcu)
  -- every inner vertex reaches an inner neighbour of the frame
  have hreach : ∀ u, (u ∈ R ∧ u ∉ C) → (restrict G I).Reachable w₀ u := by
    intro u hu
    by_contra hno
    set K := {v | (v ∈ R ∧ v ∉ C) ∧ (restrict G I).Reachable u v ∧ ∀ c ∈ C, ¬ G.Adj v c}
    have hKne : K.Nonempty := ⟨u, hu, Reachable.refl _, fun c hc hadj => hno (by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
        exact hring i hi u hu hadj.symm)⟩
    have hKcl : ∀ v ∈ K, ∀ w ∈ R, G.Adj v w → w ∈ K := by
      intro v hv w hwR hvw
      have hwC : w ∉ C := fun hwC => hv.2.2 w hwC hvw
      have hvw' : (restrict G I).Reachable u w :=
        hv.2.1.trans (Adj.reachable (G := restrict G I) ⟨hvw, hv.1, ⟨hwR, hwC⟩⟩)
      refine ⟨⟨hwR, hwC⟩, hvw', fun c hc hwc => hno ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      exact (hring i hi w ⟨hwR, hwC⟩ hwc.symm).trans hvw'.symm
    obtain ⟨v, hvK, hvC⟩ := hφ.meets_frame hC hR (fun v hv => hv.1.1) hKne hKcl
    exact hvK.1.2 hvC
  intro u v hu hv
  exact (hreach u hu).symm.trans (hreach v hv)

end GraphMinor.HP25
