module

public import GraphMinor.Compute.CrossingOpsCopy

/-!
# Installing the retained adjacency lists

After the sparsification filter builds new lists in scratch memory, three capped
copies replace the instance's start, end, and entries arrays. The cap preserves
all entries described by the lists, including when unused array entries are large.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Copy a scratch CSR encoding into the three destination arrays. -/
def installAdjProg (a_s a_e a_ent B R : ℕ) : Cmd :=
  .seq (.assign R (.op .add (.len B) (.len (B + 2))))
    (.seq (copyMinProg B a_s R (R + 1) (R + 2))
      (.seq (copyMinProg (B + 1) a_e R (R + 1) (R + 2))
        (copyMinProg (B + 2) a_ent R (R + 1) (R + 2))))

/-- Copying a CSR encoding preserves its lists and exact entry count. The input
and output arrays are separated, and the word bound covers the capping value. -/
theorem installAdjProg_exec {w N : ℕ} (a_s a_e a_ent B R : ℕ)
    (hs : a_s < B) (he : a_e < B) (hent : a_ent < B)
    (hse : a_s ≠ a_e) (hst : a_s ≠ a_ent) (het : a_e ≠ a_ent)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {s : State}
    (hadj : IsAdjList G B (B + 1) (B + 2) lists s)
    (hentries : (s.arrs (B + 2)).length = 2 * G.edgeSet.ncard)
    (hw : N + 2 * G.edgeSet.ncard + 2 < 2 ^ w) :
    ∃ s' t, Exec w (installAdjProg a_s a_e a_ent B R) s s' t ∧
      t ≤ 60 * (N + G.edgeSet.ncard + 1) ∧ IsAdjList G a_s a_e a_ent lists s' ∧
      (s'.arrs a_ent).length = 2 * G.edgeSet.ncard ∧
      (∀ a, a ≠ a_s → a ≠ a_e → a ≠ a_ent → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 3 ≤ r → s'.regs r = s.regs r) := by
  let cap := N + 2 * G.edgeSet.ncard
  let s0 := s.setReg R cap
  have hlen : (s.arrs B).length = N := hadj.1.1
  have hlen1 : (s.arrs (B + 1)).length = N := hadj.1.2.1
  have hc : cap < 2 ^ w := by dsimp [cap]; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hR1 : R ≠ R + 1 := by omega
  have hR2 : R ≠ R + 2 := by omega
  have h12 : R + 1 ≠ R + 2 := by omega
  have he0 : Exec w (.assign R (.op .add (.len B) (.len (B + 2)))) s s0 4 :=
    by
      apply Exec.assign
      simpa only [hlen, hentries] using
        (eval_add (eval_len (w := w) (s := s) (a := B) rfl (by omega))
          (eval_len (w := w) (s := s) (a := B + 2) rfl (by omega))
          (by omega))
  obtain ⟨s1, t1, he1, ht1, hd1, ha1, hr1⟩ := copyMinProg_exec (w := w) B a_s R (R + 1) (R + 2)
    (by omega) hR1 hR2 h12 (s := s0) (B := cap) (by simp [s0]) hc hw1 (by simpa [s0, hlen] using (show N < 2 ^ w by omega))
  have hr1' : s1.regs R = cap := by rw [hr1 _ hR1 hR2]; simp [s0]
  have ha1' : ∀ a, a ≠ a_s → s1.arrs a = s.arrs a := fun a ha => (ha1 a ha).trans rfl
  obtain ⟨s2, t2, he2, ht2, hd2, ha2, hr2⟩ := copyMinProg_exec (w := w) (B + 1) a_e R (R + 1) (R + 2)
    (by omega) hR1 hR2 h12 hr1' hc hw1 (by rw [ha1' _ (by omega), hlen1]; omega)
  have hr2' : s2.regs R = cap := by rw [hr2 _ hR1 hR2, hr1']
  obtain ⟨s3, t3, he3, ht3, hd3, ha3, hr3⟩ := copyMinProg_exec (w := w) (B + 2) a_ent R (R + 1) (R + 2)
    (by omega) hR1 hR2 h12 hr2' hc hw1
    (by rw [ha2 _ (by omega), ha1' _ (by omega), hentries]; omega)
  have hc1 : s3.arrs a_s = s.arrs B := by
    rw [ha3 _ hst, ha2 _ hse, hd1]
    apply map_min_of_le
    intro x hx
    have hx' : x ∈ s.arrs B := hx
    have := (IsListFamily.start_le hadj.1).1 x hx'
    dsimp [cap]; omega
  have hc2 : s3.arrs a_e = s.arrs (B + 1) := by
    rw [ha3 _ het, hd2, ha1' _ (by omega)]
    apply map_min_of_le
    intro x hx
    have := (IsListFamily.start_le hadj.1).2 x hx
    dsimp [cap]; omega
  have hc3 : s3.arrs a_ent = (s.arrs (B + 2)).map (fun x => min x cap) := by
    rw [hd3, ha2 _ (by omega), ha1' _ (by omega)]
  refine ⟨s3, 4 + (t1 + (t2 + t3)), .seq he0 (.seq he1 (.seq he2 he3)), ?_,
    IsAdjList.of_capped hadj (by dsimp [cap]; omega) hc1 hc2 hc3,
    by rw [hc3, List.length_map, hentries], ?_, ?_⟩
  · have l1 : (s0.arrs B).length = N := hlen
    have l2 : (s1.arrs (B + 1)).length = N := by rw [ha1' _ (by omega), hlen1]
    have l3 : (s2.arrs (B + 2)).length = 2 * G.edgeSet.ncard := by
      rw [ha2 _ (by omega), ha1' _ (by omega), hentries]
    rw [l1] at ht1; rw [l2] at ht2; rw [l3] at ht3
    omega
  · intro a h1 h2 h3
    rw [ha3 _ h3, ha2 _ h2, ha1' _ h1]
  · intro r hr
    rw [hr3 _ (by omega) (by omega), hr2 _ (by omega) (by omega), hr1 _ (by omega) (by omega)]
    simp [s0, show r ≠ R by omega]

/-- Installing a supported graph changes only the three CSR arrays of an instance.
The vertex marks and cycle list remain those of the input instance. -/
theorem installAdjProg_instance_exec {w N : ℕ} (a : InstArrs) (B R : ℕ)
    (hok : ArrsOk a.list B) {G H : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {lists : Fin N → List ℕ} {s : State}
    (hinst : IsInstanceAt a G S D s) (hsupp : HP25.IsSupportedOn H (↑S : Set (Fin N)))
    (hadj : IsAdjList H B (B + 1) (B + 2) lists s)
    (hentries : (s.arrs (B + 2)).length = 2 * H.edgeSet.ncard)
    (hw : N + 2 * H.edgeSet.ncard + 2 < 2 ^ w) :
    ∃ s' t, Exec w (installAdjProg a.st a.en a.ent B R) s s' t ∧
      t ≤ 60 * (N + H.edgeSet.ncard + 1) ∧ IsInstanceAt a H S D s' ∧
      (∀ x, x ∉ [a.st, a.en, a.ent] → s'.arrs x = s.arrs x) ∧
      (∀ r, r < R ∨ R + 3 ≤ r → s'.regs r = s.regs r) := by
  have hne : ∀ i j (hi : i < 5) (hj : j < 5), i ≠ j →
      a.list[i]'(by simp [InstArrs.list]; omega) ≠
        a.list[j]'(by simp [InstArrs.list]; omega) :=
    fun i j _ _ hij hh => hij ((hok.1.getElem_inj_iff).mp hh)
  obtain ⟨s', t, hex, ht, ha, hl, hframe, hr⟩ := installAdjProg_exec (w := w)
    a.st a.en a.ent B R (hok.2 _ (by simp [InstArrs.list]))
    (hok.2 _ (by simp [InstArrs.list])) (hok.2 _ (by simp [InstArrs.list]))
    (by simpa [InstArrs.list] using hne 1 2 (by decide) (by decide) (by decide))
    (by simpa [InstArrs.list] using hne 1 3 (by decide) (by decide) (by decide))
    (by simpa [InstArrs.list] using hne 2 3 (by decide) (by decide) (by decide)) hadj hentries hw
  refine ⟨s', t, hex, ht, ⟨hsupp, ?_, ⟨lists, ha⟩, hl, ?_⟩, ?_, hr⟩
  · rw [hframe _ (by simpa [InstArrs.list] using hne 0 1 (by decide) (by decide) (by decide))
      (by simpa [InstArrs.list] using hne 0 2 (by decide) (by decide) (by decide))
      (by simpa [InstArrs.list] using hne 0 3 (by decide) (by decide) (by decide))]
    exact hinst.2.1
  · rw [hframe _ (by simpa [InstArrs.list] using hne 4 1 (by decide) (by decide) (by decide))
      (by simpa [InstArrs.list] using hne 4 2 (by decide) (by decide) (by decide))
      (by simpa [InstArrs.list] using hne 4 3 (by decide) (by decide) (by decide))]
    exact hinst.2.2.2.2
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact hframe x hx.1 hx.2.1 hx.2.2

end GraphMinor.Compute.Crossing
