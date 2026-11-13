module

public import GraphMinor.Compute.TwoPathsSweep

/-!
# The sweep over all components of `H - C`

`sweepProg` runs, for each vertex `v` in turn, the search of `TwoPathsSearch.lean` from `v` (when
`v` is free and not yet reached) and then the scan of the new segment of the queue
(`TwoPathsSweep.lean`). Each segment is one component of `H - C` (`seg_reach`), so at the end
either a pair was found (`PairOK`), or no component has two attachments that are apart
(`NoComp`).

The time of one round depends on the size of the component, so the rounds are counted with a
potential (`forUp_pot`): `38` per vertex in the queue and `119` per adjacency entry of a vertex in
the queue. The whole sweep takes `O(n + m)` steps.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### A counting loop with a potential -/

/-- **A counting loop with a potential.** Each round costs at most `B` plus the rise of the
potential `Φ`. -/
theorem forUp_pot {w : ℕ} (I : ℕ → State → Prop) (Φ : State → ℕ) (N B : ℕ) {r_i : Reg}
    {hi : Expr} {body : Cmd} (hw : 1 < 2 ^ w) (hN : N < 2 ^ w)
    (hhi : ∀ i ≤ N, ∀ s, I i s → s.regs r_i = i ∧ hi.eval w s = some N)
    (hbody : ∀ i < N, ∀ s, I i s → ∃ s' t, Exec w body s s' t ∧
      t + Φ s ≤ B + Φ (s'.setReg r_i (i + 1)) ∧ I (i + 1) (s'.setReg r_i (i + 1)) ∧
      s'.regs r_i = i) :
    ∀ i₀ ≤ N, ∀ s, I i₀ s → ∃ s' t, Exec w (forUp r_i hi body) s s' t ∧
      t + Φ s ≤ (hi.cost + 2) + (N - i₀) * (hi.cost + 6 + B) + Φ s' ∧ I N s' := by
  intro i₀ hi₀
  induction hd : N - i₀ generalizing i₀ with
  | zero =>
    have : i₀ = N := by omega
    subst this
    intro s hs
    obtain ⟨hreg, hev⟩ := hhi i₀ le_rfl s hs
    have hcond : (Expr.op .lt (.reg r_i) hi).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg, hev, hN, show 0 < 2 ^ w by omega]
    refine ⟨s, _, .while_false hcond, ?_, hs⟩
    simp only [Expr.cost]; omega
  | succ d ih =>
    intro s hs
    obtain ⟨hreg, hev⟩ := hhi i₀ hi₀ s hs
    have hlt : i₀ < N := by omega
    have hcond : (Expr.op .lt (.reg r_i) hi).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg, hev, hN, hlt,
        show i₀ < 2 ^ w by omega, hw]
    obtain ⟨s₁, t₁, hex₁, ht₁, hI₁, hreg₁⟩ := hbody i₀ hlt s hs
    have hinc : (Expr.op .add (.reg r_i) (.const 1)).eval w s₁ = some (i₀ + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg₁, show i₀ < 2 ^ w by omega, hw,
        show i₀ + 1 < 2 ^ w by omega]
    have hstep : Exec w (.seq body (.assign r_i (.op .add (.reg r_i) (.const 1)))) s
        (s₁.setReg r_i (i₀ + 1)) (t₁ + 4) := .seq hex₁ (.assign hinc)
    obtain ⟨s₂, t₂, hex₂, ht₂, hI₂⟩ := ih (i₀ + 1) (by omega) (by omega) _ hI₁
    refine ⟨s₂, _, .while_true hcond (by omega) hstep hex₂, ?_, hI₂⟩
    rw [Nat.add_mul, Nat.one_mul]
    simp only [Expr.cost] at ht₂ ⊢
    omega

/-! ### Walks off the cycle -/

theorem reachable_restrict_of_walk {H : SimpleGraph (Fin n)} {S : Set (Fin n)} :
    ∀ {a b : Fin n} (W : H.Walk a b), (∀ z ∈ W.support, z ∈ S) → (restrict H S).Reachable a b
  | _, _, .nil, _ => Reachable.refl _
  | _, _, .cons h W, hW => by
    refine Reachable.trans ?_ (reachable_restrict_of_walk W fun z hz =>
      hW z (List.mem_cons_of_mem _ hz))
    exact Adj.reachable ⟨h, hW _ (List.mem_cons_self), hW _ (List.mem_cons_of_mem _
      W.start_mem_support)⟩

theorem exists_walk_of_reachable_restrict {H : SimpleGraph (Fin n)} {S : Set (Fin n)} {a b : Fin n}
    (h : (restrict H S).Reachable a b) (ha : a ∈ S) :
    ∃ W : H.Walk a b, ∀ z ∈ W.support, z ∈ S := by
  obtain ⟨W⟩ := h
  induction W with
  | nil => exact ⟨.nil, by simpa using ha⟩
  | cons hadj W ih =>
    obtain ⟨W', hW'⟩ := ih hadj.2.2
    refine ⟨.cons hadj.1 W', fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ha
    · exact hW' z hz


/-! ### Facts about the search state -/

/-- The invariant of the search only looks at registers `60..70` and arrays `60, 61, 62`. -/
theorem SInv.transfer {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {src : List ℕ} {s₀ s s' : State}
    {items : List ℕ} {h : ℕ} (hs : SInv G L0 src s₀ items h s)
    (hr : ∀ r, 60 ≤ r → r < 71 → s'.regs r = s.regs r)
    (ha : ∀ a, a = aLab ∨ a = aPar ∨ a = aQue → s'.arrs a = s.arrs a) :
    SInv G L0 src s' items h s' := by
  obtain ⟨-, hq, hnd, hlt, hfree, hlab, ⟨p, hpar, hpok⟩, hcl, hhit, hsrcs⟩ := hs
  refine ⟨⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩, ?_, hnd, hlt, hfree,
    by rw [ha _ (Or.inl rfl)]; exact hlab, ⟨p, by rw [ha _ (Or.inr (Or.inl rfl))]; exact hpar,
      hpok⟩, hcl, by rw [hr _ (by decide) (by decide), hr _ (by decide) (by decide)]; exact hhit,
    hsrcs⟩
  exact hq.of_eq (ha _ (Or.inr (Or.inr rfl))) (hr _ (by decide) (by decide))
    (hr _ (by decide) (by decide))

/-- The labels of the sweep: `2` on the cycle, `0` elsewhere. -/
def labT (T : List (Fin n)) (x : Fin n) : ℕ := if x ∈ T then 2 else 0

theorem labT_eq_zero {T : List (Fin n)} {x : Fin n} : labT T x = 0 ↔ x ∉ T := by
  unfold labT; split_ifs with h <;> simp [h]

/-- **The root of a new vertex.** A vertex that the search reached after the old reached set
`items` (closed, and containing every old source) was reached from a new source, through vertices
off `T`. -/
theorem seg_root {H : SimpleGraph (Fin n)} {T : List (Fin n)} {src src' items extra : List ℕ}
    {p : Fin n → ℕ} (hp : ParentOK H src' (items ++ extra) p)
    (hfree : ∀ x : Fin n, x.1 ∈ items ++ extra → labT T x = 0)
    (hcl : ∀ u : Fin n, u.1 ∈ items → ∀ v, H.Adj u v → labT T v ≠ 0 ∨ v.1 ∈ items)
    (hsrcs : ∀ x : Fin n, x.1 ∈ src → labT T x = 0 → x.1 ∈ items)
    (hnd : (items ++ extra).Nodup) (x : Fin n) (hx : x.1 ∈ extra) :
    ∃ r : Fin n, r.1 ∈ src' ∧ r.1 ∉ src ∧ (restrict H {v | v ∉ T}).Reachable r x := by
  have hxm : x.1 ∈ items ++ extra := List.mem_append_right _ hx
  obtain ⟨r, W, -, hr, hsupp, -, -⟩ :=
    exists_walk_of_parentOK hp ((items ++ extra).idxOf x.1 + 1) x hxm (by omega)
  have hoffW : ∀ z ∈ W.support, z ∈ {v : Fin n | v ∉ T} := fun z hz =>
    labT_eq_zero.1 (hfree z (hsupp z hz).1)
  refine ⟨r, hr, fun hrs => ?_, reachable_restrict_of_walk W hoffW⟩
  have hri : r.1 ∈ items := hsrcs r hrs (hfree r (hsupp r W.start_mem_support).1)
  have hxi : x.1 ∈ items := mem_of_walk_closed hcl W hri (fun z hz => hfree z (hsupp z hz).1)
  exact List.disjoint_of_nodup_append hnd hxi hx

theorem popDeg_queue {lists : Fin n → List ℕ} {items : List ℕ} {h : ℕ} {s : State}
    (hq : IsQueueHistory aQue rHead rTail n items h s) :
    popDeg lists (s.arrs aQue) items.length = popDeg lists items items.length := by
  obtain ⟨hlen, hle, -, -, -, hel⟩ := hq
  unfold popDeg
  congr 2
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_take]
  exact hel i (by simpa using h₂)


theorem popDeg_append_length (lists : Fin n → List ℕ) (items e : List ℕ) :
    popDeg lists (items ++ e) items.length = popDeg lists items items.length := by
  simp [popDeg]

theorem cdist_self {k p : ℕ} (hk : 0 < k) (hp : p ≤ k) : cdist k p p = 0 := by
  unfold cdist; rw [show p + k - p = k by omega, Nat.mod_self]

theorem not_apart_self {k p : ℕ} (hk : 0 < k) (hp : p ≤ k) : ¬ Apart k p p := by
  unfold Apart; rw [cdist_self hk hp]; omega

/-- At the end of the scan of a segment with nothing found, no two attachments of the segment
are apart. -/
theorem AttOK.not_apart {H : SimpleGraph (Fin n)} {T : List (Fin n)} {seg : List ℕ} {s : State}
    (h : AttOK H T seg (fun a _ => a.1 ∈ seg) s) {u u' y y' : Fin n} (hu : u.1 ∈ seg)
    (hu' : u'.1 ∈ seg) (hy : y ∈ T) (hy' : y' ∈ T) (huy : H.Adj u y) (huy' : H.Adj u' y') :
    ¬ Apart T.length (tpos T y') (tpos T y) := by
  have hk : 0 < T.length := List.length_pos_of_mem hy
  have hpy := tpos_le hy
  have hpy' := tpos_le hy'
  obtain ⟨hA, hB⟩ := h
  by_cases hF : s.regs rFp = 0
  · exact absurd hy ((hA hF).2 u y hu huy)
  obtain ⟨fx, fu, a1, -, -, -, -, -, a7⟩ := hB hF
  rcases a7 with ⟨-, b2⟩ | ⟨sx, su, b1, -, -, -, -, -, -, b8, b9⟩
  · rw [b2 u y hu huy hy, b2 u' y' hu' huy' hy']
    exact not_apart_self hk (tpos_le a1)
  · have hpf : 1 ≤ tpos T fx ∧ tpos T fx ≤ T.length := ⟨tpos_pos, tpos_le a1⟩
    have hps : 1 ≤ tpos T sx ∧ tpos T sx ≤ T.length := ⟨tpos_pos, tpos_le b1⟩
    rcases b9 u y hu huy hy with e | e <;> rcases b9 u' y' hu' huy' hy' with e' | e' <;>
      rw [e, e']
    · exact not_apart_self hk hpf.2
    · exact b8
    · rw [apart_symm hpf hps]; exact b8
    · exact not_apart_self hk hps.2

theorem SFrame.keeps {s₀ s : State} (h : SFrame s₀ s) :
    Keeps [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70] [aLab, aPar, aQue] s₀ s := by
  refine ⟨fun r hr => h.1 r ?_, fun a ha => h.2 a (fun e => ha (by simp [e]))
    (fun e => ha (by simp [e])) (fun e => ha (by simp [e]))⟩
  by_contra hc
  simp only [not_or, not_lt, not_le] at hc
  obtain ⟨h1, h2⟩ := hc
  apply hr
  interval_cases r <;> simp

/-! ### One round of the sweep -/

/-- One component: push `rV2`, search, scan the new segment. -/
def compBody : Cmd :=
  .seq (.assign rSt (.reg rTail)) (.seq pushV (.seq (searchLoop aStart aEnd aEnt) segScan))

/-- One round of the sweep, skipped once a pair is found. -/
def compStep : Cmd := .ite (.op .eq (.reg rFound) (.const 0)) compBody .skip

/-- The registers that the sweep writes. -/
def sweepRegs : List ℕ := [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, rV2, rSt] ++ segRegs

/-- No component of `H - T` met by `items` has two attachments that are apart. -/
def NoComp (H : SimpleGraph (Fin n)) (T : List (Fin n)) (items : List ℕ) : Prop :=
  ∀ u u' y y' : Fin n, u.1 ∈ items → u'.1 ∈ items → (restrict H {v | v ∉ T}).Reachable u u' →
    y ∈ T → y' ∈ T → H.Adj u y → H.Adj u' y' → ¬ Apart T.length (tpos T y') (tpos T y)

/-- The result of the sweep after the vertices below `v`. -/
def SweepRes (H : SimpleGraph (Fin n)) (T : List (Fin n)) (items : List ℕ) (v : ℕ) (s : State) :
    Prop :=
  (s.regs rFound = 0 ∧ NoChord H T (fun x _ => x ∈ T) ∧ NoComp H T items ∧
    ∀ x : Fin n, x.1 < v → x ∉ T → x.1 ∈ items) ∨ (s.regs rFound = 1 ∧ PairOK H T s)

/-- The potential of the sweep. -/
def sweepPot (lists : Fin n → List ℕ) (s : State) : ℕ :=
  38 * s.regs rTail + 119 * popDeg lists (s.arrs aQue) (s.regs rTail)

/-- What the sweep needs of the state it starts from. -/
structure SweepPre (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ) (T : List (Fin n))
    (s : State) : Prop where
  adj : IsAdjList H aStart aEnd aEnt lists s
  pos : s.arrs aPos = posArr T
  k : s.regs rk = T.length
  n : s.regs 40 = n

theorem SweepPre.keeps {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ} {T : List (Fin n)}
    {s₀ s : State} (h : SweepPre H lists T s₀) (hk : Keeps sweepRegs [aLab, aPar, aQue] s₀ s) :
    SweepPre H lists T s := by
  refine ⟨h.adj.of_arrs_eq (hk.2 _ (by simp)) (hk.2 _ (by simp)) (hk.2 _ (by simp)), ?_, ?_, ?_⟩
  · rw [hk.2 _ (by simp)]; exact h.pos
  · rw [hk.1 _ (by simp [sweepRegs, segRegs])]; exact h.k
  · rw [hk.1 _ (by simp [sweepRegs, segRegs])]; exact h.n

/-- The invariant of the sweep after the vertices below `v`. -/
def GInv (H : SimpleGraph (Fin n)) (T : List (Fin n)) (s₀ : State) (v : ℕ) (s : State) :
    Prop :=
  Keeps sweepRegs [aLab, aPar, aQue] s₀ s ∧ s.regs rV2 = v ∧ ∃ items src : List ℕ,
    SInv H (labT T) src s items items.length s ∧ SweepRes H T items v s


theorem sweepPot_eq {lists : Fin n → List ℕ} {items : List ℕ} {h : ℕ} {s : State}
    (hq : IsQueueHistory aQue rHead rTail n items h s) :
    sweepPot lists s = 38 * items.length + 119 * popDeg lists items items.length := by
  unfold sweepPot
  rw [hq.2.2.2.1, popDeg_queue hq]

/-- **One round of the sweep.** -/
theorem compStep_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hpre : SweepPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (v : ℕ) (hv : v < n) (s : State) (hs : GInv H T s₀ v s) :
    ∃ s' t, Exec w compStep s s' t ∧
      t + sweepPot lists s ≤ 40 + sweepPot lists (s'.setReg rV2 (v + 1)) ∧
      GInv H T s₀ (v + 1) (s'.setReg rV2 (v + 1)) ∧ s'.regs rV2 = v := by
  obtain ⟨hk, hrv, items, src, hsi, hres⟩ := hs
  have hpre' := hpre.keeps hk
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hL0 : ∀ x, labT T x ≤ 3 := fun x => by unfold labT; split_ifs <;> omega
  have hfv : s.regs rFound ≤ 1 := by rcases hres with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have eF : (Expr.op .eq (.reg rFound) (.const 0)).eval w s =
      some (if s.regs rFound = 0 then 1 else 0) :=
    eq_eval (reg_eval rfl (by omega)) (by simp [checkWord, hw1]) hw1
  have hpotR : ∀ st : State, st.regs rTail = s.regs rTail → st.arrs aQue = s.arrs aQue →
      sweepPot lists st = sweepPot lists s := fun st h1 h2 => by unfold sweepPot; rw [h1, h2]
  rcases hres with ⟨hf0, hnoch, hnoc, hall⟩ | ⟨hf1, hp⟩
  swap
  · -- a pair was found: skip
    have hex : Exec w compStep s s (3 + 1) := .ite_false (by rw [eF]; simp [hf1]) (.skip _)
    refine ⟨s, _, hex, by rw [hpotR (s.setReg rV2 (v + 1)) (by simp) (by simp)]; omega, ⟨hk.setReg (by simp [sweepRegs])
      _, by simp, items, src, hsi.transfer (fun r h1 h2 => by
        have : r ≠ rV2 := by rintro rfl; exact absurd h2 (by decide)
        simp [this]) (fun a _ => by simp), Or.inr ⟨by simp [hf1], hp.of_regs (by simp) (by simp)
          (by simp) (by simp)⟩⟩, hrv⟩
  -- nothing found yet: the component of `v`
  have hlen : items.length ≤ n := length_le_of_nodup_lt hsi.nodup hsi.lt
  have htail : s.regs rTail = items.length := hsi.queue.2.2.2.1
  set s₁ := s.setReg rSt items.length with hs₁
  have hex₁ : Exec w (.assign rSt (.reg rTail)) s s₁ (1 + 1) :=
    .assign (reg_eval htail (by omega))
  have hsi₁ : SInv H (labT T) src s₁ items items.length s₁ :=
    hsi.transfer (fun r h1 h2 => by
      have : r ≠ rSt := by rintro rfl; exact absurd h2 (by decide)
      simp [s₁, this]) (fun a _ => by simp [s₁])
  have hk₁ : Keeps sweepRegs [aLab, aPar, aQue] s₀ s₁ := hk.setReg (by simp [sweepRegs]) _
  have hpre₁ := hpre.keeps hk₁
  obtain ⟨s₂, t₂, hex₂, ht₂, hcase⟩ := pushV_exec H (labT T) hL0 src s₁ hpre₁.n hw4 hnw items s₁
    hsi₁ ⟨v, hv⟩ (by simp [s₁, hrv])
  -- after the push: `items₁`, `src₁`
  obtain ⟨items₁, src₁, hsi₂, hit₁, hsrc₁, hvcase⟩ : ∃ items₁ src₁ : List ℕ,
      SInv H (labT T) src₁ s₁ items₁ items.length s₂ ∧ (∃ e, items₁ = items ++ e) ∧
      (∀ r : Fin n, r.1 ∈ src₁ → r.1 ∉ src → r.1 = v) ∧
      (v ∈ items₁ ∨ labT T ⟨v, hv⟩ ≠ 0) := by
    rcases hcase with ⟨hni, hl0, hs'⟩ | ⟨hor, hs'⟩
    · refine ⟨items ++ [v], src ++ [v], hs', ⟨_, rfl⟩, fun r h1 h2 => ?_, Or.inl (by simp)⟩
      rw [List.mem_append, List.mem_singleton] at h1
      rcases h1 with h | h
      · exact absurd h h2
      · exact h
    · refine ⟨items, src, hs', ⟨[], by simp⟩, fun r h1 h2 => absurd h1 h2, ?_⟩
      rcases hor with h | h
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨e₁, rfl⟩ := hit₁
  obtain ⟨s₃, t₃, extra, hex₃, -, ht₃, hsi₃⟩ := searchLoop_exec H lists aStart aEnd aEnt
    (by decide) (by decide) (by decide) (labT T) hL0 src₁ s₁ hpre₁.adj
    (by rw [hk₁.2 _ (by simp)]; exact hent) hpre₁.n hw4 hnw _ (items ++ e₁) items.length s₂ rfl
    hsi₂
  set itf := items ++ e₁ ++ extra with hitf
  have hitf' : itf = items ++ (e₁ ++ extra) := by simp [itf]
  set seg := itf.drop items.length with hseg
  have hseg' : seg = e₁ ++ extra := by simp [seg, hitf']
  -- the segment is off the cycle and connected
  have hoff : ∀ a : Fin n, a.1 ∈ seg → a ∉ T := fun a ha =>
    labT_eq_zero.1 (hsi₃.free a (List.mem_of_mem_drop ha))
  obtain ⟨p, -, hpok⟩ := hsi₃.par
  have hcl : ∀ u : Fin n, u.1 ∈ items → ∀ v', H.Adj u v' → labT T v' ≠ 0 ∨ v'.1 ∈ items :=
    fun u hu v' hv' => hsi.closed u (by simpa using hu) v' hv'
  have hroot : ∀ x : Fin n, x.1 ∈ seg → (restrict H {v | v ∉ T}).Reachable ⟨v, hv⟩ x := by
    intro x hx
    rw [hseg'] at hx
    rw [hitf'] at hpok
    obtain ⟨r, hr1, hr2, hreach⟩ := seg_root (src := src) hpok
      (by rw [← hitf']; exact hsi₃.free) hcl hsi.srcs (by rw [← hitf']; exact hsi₃.nodup) x hx
    have : r = ⟨v, hv⟩ := Fin.ext (hsrc₁ r hr1 hr2)
    rw [← this]; exact hreach
  have hR : ∀ a b : Fin n, a.1 ∈ seg → b.1 ∈ seg → (restrict H {v | v ∉ T}).Reachable a b :=
    fun a b ha hb => (hroot a ha).symm.trans (hroot b hb)
  -- the scan of the segment
  have hkeep₃ : ∀ r, r < 60 ∨ 71 ≤ r → s₃.regs r = s₁.regs r := hsi₃.frame.1
  have hkeepA₃ : ∀ a, a ≠ aLab → a ≠ aPar → a ≠ aQue → s₃.arrs a = s₁.arrs a := hsi₃.frame.2
  have hspre : SegPre H lists T itf items.length s₃ := by
    refine ⟨hpre₁.adj.of_arrs_eq (hkeepA₃ _ (by decide) (by decide) (by decide))
      (hkeepA₃ _ (by decide) (by decide) (by decide)) (hkeepA₃ _ (by decide) (by decide)
        (by decide)), by rw [hkeepA₃ _ (by decide) (by decide) (by decide)]; exact hpre₁.pos,
      by rw [hkeep₃ _ (Or.inr (by decide))]; exact hpre₁.k, fun m hm => ?_,
      hsi₃.queue.2.2.2.1, hsi₃.lt, by simp [itf], hsi₃.nodup⟩
    obtain ⟨hl, hle, hhd, htl, hle2, hel⟩ := hsi₃.queue
    exact ⟨by rw [hl]; exact lt_of_lt_of_le hm (length_le_of_nodup_lt hsi₃.nodup hsi₃.lt),
      hel m hm⟩
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hres₄⟩ := segScan_exec H lists T hT hk4 hn itf items.length
    hoff hR s₃ hspre (by
      rw [hkeepA₃ _ (by decide) (by decide) (by decide), hk₁.2 _ (by simp)]; exact hent)
    (by rw [hkeep₃ _ (Or.inr (by decide))]; simp [s₁])
    (by rw [hkeep₃ _ (Or.inr (by decide))]; simp [s₁, hf0])
  set s₅ := s₄.setReg rV2 (v + 1) with hs₅
  have hex : Exec w compStep s s₄ (3 + (2 + (t₂ + (t₃ + t₄)))) :=
    .ite_true eF (by simp [hf0]) (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))
  have hr₅ : ∀ r, 60 ≤ r → r < 71 → s₅.regs r = s₃.regs r := by
    intro r h1 h2
    have h3 : r ≠ rV2 := by rintro rfl; exact absurd h2 (by decide)
    have h4 : r ∉ segRegs := by interval_cases r <;> decide
    rw [hs₅, State.setReg_regs_ne _ _ h3, hk₄.1 r h4]
  have ha₅ : ∀ a, s₅.arrs a = s₃.arrs a := fun a => by
    rw [hs₅, State.setReg_arrs, hk₄.2 a (by simp)]
  have hsi₅ : SInv H (labT T) src₁ s₅ itf itf.length s₅ :=
    hsi₃.transfer hr₅ (fun a _ => ha₅ a)
  have hsplit : itf = items ++ seg := by rw [hseg', hitf']
  have hnd : (items ++ seg).Nodup := by rw [← hsplit]; exact hsi₃.nodup
  have hfree : ∀ z : Fin n, z.1 ∈ itf → z ∉ T := fun z hz => labT_eq_zero.1 (hsi₃.free z hz)
  have hcross : ∀ u u' : Fin n, u.1 ∈ items → u'.1 ∈ seg →
      ¬ (restrict H {v | v ∉ T}).Reachable u u' := by
    intro u u' hu hu' hreach
    obtain ⟨W, hW⟩ := exists_walk_of_reachable_restrict hreach
      (hfree u (by rw [hsplit]; exact List.mem_append_left _ hu))
    have := mem_of_walk_closed hcl W hu (fun z hz => labT_eq_zero.2 (hW z hz))
    exact List.disjoint_of_nodup_append hnd this hu'
  refine ⟨s₄, _, hex, ?_, ⟨?_, by simp [s₅], itf, src₁, hsi₅, ?_⟩, ?_⟩
  · -- the time
    rw [sweepPot_eq hsi.queue, sweepPot_eq hsi₅.queue]
    have q1 := popDeg_append_length lists items e₁
    have q2 : popDeg lists itf items.length = popDeg lists items items.length := by
      rw [hsplit]; exact popDeg_append_length lists items seg
    have hle : items.length ≤ itf.length := by rw [hsplit]; simp
    have hmono := popDeg_add lists itf items.length (itf.length - items.length) (by omega)
    rw [Nat.add_sub_cancel' hle] at hmono
    have hpd0 : popDeg lists itf items.length ≤ popDeg lists itf itf.length := by
      rw [hmono]; omega
    omega
  · -- the frame
    have hk₃ : Keeps sweepRegs [aLab, aPar, aQue] s₀ s₃ :=
      hk₁.trans hsi₃.frame.keeps (by decide) (by decide)
    exact (hk₃.trans hk₄ (by decide) (by simp)).setReg (by simp [sweepRegs]) _
  · -- the result
    rcases hres₄ with ⟨h0, hatt⟩ | ⟨h1, hp⟩
    · refine Or.inl ⟨by simp [s₅, h0], hnoch, ?_, ?_⟩
      · intro u u' y y' hu hu' hreach hy hy' huy huy'
        rw [hsplit, List.mem_append] at hu hu'
        rcases hu with hu | hu <;> rcases hu' with hu' | hu'
        · exact hnoc u u' y y' hu hu' hreach hy hy' huy huy'
        · exact absurd hreach (hcross u u' hu hu')
        · exact absurd hreach.symm (hcross u' u hu' hu)
        · exact hatt.not_apart hu hu' hy hy' huy huy'
      · intro x hx hxT
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
        · rw [hsplit]; exact List.mem_append_left _ (hall x hx hxT)
        · rcases hvcase with h | h
          · rw [hx, hitf]; exact List.mem_append_left _ h
          · exact absurd (by
              have : x = ⟨v, hv⟩ := Fin.ext hx
              rw [this]; by_contra hc; exact h (labT_eq_zero.2 hc)) hxT
    · exact Or.inr ⟨by simp [s₅, h1], hp.of_regs (by simp [s₅]) (by simp [s₅]) (by simp [s₅])
        (by simp [s₅])⟩
  · rw [hk₄.1 _ (by simp [segRegs]), hsi₃.frame.1 _ (Or.inr (by decide))]
    simp [s₁, hrv]


/-! ### The sweep -/

/-- The sweep: an empty search state, then one round for each vertex. -/
def sweepProg : Cmd :=
  .seq (.alloc aPar (.reg 40)) (.seq (queueInit aQue rHead rTail (.reg 40))
    (.seq (.assign rHit (.reg 40)) (.seq (.assign rV2 (.const 0)) (forUp rV2 (.reg 40) compStep))))

/-- **The sweep.** From the labels `labT T` and the result of the chord scan, the sweep ends with
a pair (`PairOK`), or with no chord and no component of `H - T` with two attachments that are
apart, every vertex off `T` having been reached. It takes at most `13 + 87 n + 119 M` steps. -/
theorem sweepProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hpre : SweepPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hlab : s₀.arrs aLab = List.ofFn (labT T)) (hch : ChordRes H T (fun x _ => x ∈ T) s₀) :
    ∃ s' t, Exec w sweepProg s₀ s' t ∧ t ≤ 13 + 87 * n + 119 * totalAdjEntries lists ∧
      Keeps sweepRegs [aLab, aPar, aQue] s₀ s' ∧ ∃ items : List ℕ,
        (s'.regs rFound = 0 ∧ NoChord H T (fun x _ => x ∈ T) ∧ NoComp H T items ∧
          ∀ x : Fin n, x ∉ T → x.1 ∈ items) ∨ (s'.regs rFound = 1 ∧ PairOK H T s') := by
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have h40 : (Expr.reg 40).eval w s₀ = some n := reg_eval hpre.n hnw
  set s₁ := s₀.setArr aPar (List.replicate n 0) with hs₁
  set s₂ := s₁.setArr aQue (List.replicate n 0) with hs₂
  set s₃ := s₂.setReg rHead 0 with hs₃
  set s₄ := s₃.setReg rTail 0 with hs₄
  set s₅ := s₄.setReg rHit n with hs₅
  set s₆ := s₅.setReg rV2 0 with hs₆
  have hqi : Exec w (queueInit aQue rHead rTail (.reg 40)) s₁ s₄ ((1 + n) + ((1 + 1) + (1 + 1))) :=
    .seq (.alloc (reg_eval (by simp [s₁, hpre.n]) hnw))
      (.seq (.assign (by simp [checkWord])) (.assign (by simp [checkWord])))
  have hhit : Exec w (.assign rHit (.reg 40)) s₄ s₅ (1 + 1) :=
    .assign (reg_eval (by simp [s₄, s₃, s₂, s₁, hpre.n]) hnw)
  have hv0 : Exec w (.assign rV2 (.const 0)) s₅ s₆ (1 + 1) := .assign (by simp [checkWord])
  have hk₆ : Keeps sweepRegs [aLab, aPar, aQue] s₀ s₆ :=
    (((((Keeps.refl _ _ s₀).setArr (by simp) _).setArr (by simp) _).setReg
      (by simp [sweepRegs]) _).setReg (by simp [sweepRegs]) _ |>.setReg (by simp [sweepRegs])
        _).setReg (by simp [sweepRegs]) _
  have hI0 : GInv H T s₀ 0 s₆ := by
    refine ⟨hk₆, by simp [s₆], [], [], ⟨⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩, ?_, List.nodup_nil,
      by simp, by simp, ?_, ⟨fun _ => 0, ?_, fun x hx => by simp at hx⟩, by simp, ?_, by simp⟩, ?_⟩
    · exact ⟨by simp [s₆, s₅, s₄, s₃, s₂], by simp, by simp [s₆, s₅, s₄, s₃],
        by simp [s₆, s₅, s₄], le_rfl, fun i hi => by simp at hi⟩
    · simp only [List.not_mem_nil, if_false]
      simp [s₆, s₅, s₄, s₃, s₂, s₁, hlab]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, List.ofFn_const]
    · exact Or.inl ⟨by simp [s₆, s₅], fun v ⟨u, hu, _⟩ => by simp at hu⟩
    · have hf : s₆.regs rFound = s₀.regs rFound := by simp [s₆, s₅, s₄, s₃, s₂, s₁]
      rcases hch with ⟨h0, hno⟩ | ⟨h1, hp⟩
      · exact Or.inl ⟨by rw [hf, h0], hno, fun u _ _ _ hu => by simp at hu,
          fun x hx => by omega⟩
      · exact Or.inr ⟨by rw [hf, h1], hp.of_regs (by simp [s₆, s₅, s₄, s₃, s₂, s₁])
          (by simp [s₆, s₅, s₄, s₃, s₂, s₁]) (by simp [s₆, s₅, s₄, s₃, s₂, s₁])
          (by simp [s₆, s₅, s₄, s₃, s₂, s₁])⟩
  have hloop := forUp_pot (GInv H T s₀) (sweepPot lists) n 40 (r_i := rV2) (hi := .reg 40)
    (body := compStep) (w := w) hw1 hnw
    (fun i _ st hst => ⟨hst.2.1, reg_eval (by
      rw [hst.1.1 _ (by simp [sweepRegs, segRegs])]; exact hpre.n) hnw⟩)
    (fun i hi st hst => compStep_exec H lists T hT hk4 hn s₀ hpre hent i hi st hst)
    0 (Nat.zero_le _) s₆ hI0
  obtain ⟨s₇, t₇, hex₇, ht₇, hk₇, -, items, src, hsi, hres⟩ := hloop
  have hpot0 : sweepPot lists s₆ = 0 := by simp [sweepPot, s₆, s₅, s₄, popDeg]
  have hpot7 : sweepPot lists s₇ ≤ 38 * n + 119 * totalAdjEntries lists := by
    rw [sweepPot_eq hsi.queue]
    have h1 := length_le_of_nodup_lt hsi.nodup hsi.lt
    have h2 : popDeg lists items items.length ≤ totalAdjEntries lists := by
      unfold popDeg; rw [List.take_length]; exact sum_degOf_le lists hsi.nodup hsi.lt
    omega
  refine ⟨s₇, _, .seq (.alloc h40) (.seq hqi (.seq hhit (.seq hv0 hex₇))), ?_, hk₇, items, ?_⟩
  · simp only [Expr.cost] at ht₇ ⊢
    omega
  · rcases hres with ⟨h0, hno, hnc, hall⟩ | h1
    · exact Or.inl ⟨h0, hno, hnc, fun x hx => hall x x.2 hx⟩
    · exact Or.inr h1

end GraphMinor.Compute.TwoPaths
