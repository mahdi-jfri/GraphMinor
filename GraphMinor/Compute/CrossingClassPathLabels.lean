module

public import GraphMinor.Compute.CrossingClassPath
public import GraphMinor.Compute.Array

/-!
# Labels for a bridge path search

Section 5.2 of `docs/crossing/crossing_extractor.tex` restricts a component-bridge search to the
component
and the two selected endpoints. This file initializes the labels from an array listing the
allowed inner vertices. It blocks every vertex first and then frees the listed vertices.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Compute.TwoPaths

/-- An array holding the allowed inner vertices for one path search. -/
abbrev aBridgeAllowed : Arr := 126
/-- Counter used only while initializing search labels. -/
abbrev rBridgeLabel : Reg := 142

/-- Free the vertices of `A` and block all other vertices. -/
def bridgeLabels {n : ℕ} (A : List (Fin n)) (v : Fin n) : ℕ :=
  if v ∈ A then 0 else 2

/-- Initialize the label array from the allowed-vertex array. -/
def bridgeLabelProg : Cmd :=
  .seq (.alloc aLab (.reg 40))
    (.seq (fillArr aLab (.len aLab) (.const 2) rBridgeLabel)
      (.seq (.assign rBridgeLabel (.const 0))
        (forUp rBridgeLabel (.len aBridgeAllowed)
          (.write aLab (.read aBridgeAllowed (.reg rBridgeLabel)) (.const 0)))))

private theorem bridgeLabels_append {n : ℕ} (A : List (Fin n)) (u : Fin n) :
    Function.update (bridgeLabels A) u 0 = bridgeLabels (A ++ [u]) := by
  funext v
  by_cases h : v = u
  · subst h; simp [bridgeLabels]
  · simp [bridgeLabels, h]

/-- Initialize labels in linear time, preserving every array except the labels and every
register except the loop counter. The input is a list of vertices and the graph size. -/
theorem bridgeLabelProg_exec {w n : ℕ} (A : List (Fin n)) (s : State)
    (hrn : s.regs 40 = n) (hA : s.arrs aBridgeAllowed = A.map Fin.val)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hlen : A.length < 2 ^ w) :
    ∃ s' t, Exec w bridgeLabelProg s s' t ∧
      t ≤ 20 + 13 * n + 12 * A.length ∧
      s'.arrs aLab = List.ofFn (bridgeLabels A) ∧
      (∀ r ≠ rBridgeLabel, s'.regs r = s.regs r) ∧
      (∀ a ≠ aLab, s'.arrs a = s.arrs a) := by
  let s₁ := s.setArr aLab (List.replicate n 0)
  have hex₁ : Exec w (.alloc aLab (.reg 40)) s s₁ (1 + n) :=
    .alloc (reg_eval hrn hn)
  obtain ⟨s₂, t₂, hex₂, ht₂, hlab₂, _⟩ :=
    Triple.fillArr_const aLab 2 rBridgeLabel (List.replicate n 0) (by omega)
      (by simpa using hn) hw s₁ (by simp [s₁])
  have hA₂ : s₂.arrs aBridgeAllowed = A.map Fin.val := by
    rw [hex₂.arrs_eq_of_not_mem_writtenArrs (by
      simp [fillArr, forUp, Cmd.writtenArrs])]
    exact hA
  let s₃ := s₂.setReg rBridgeLabel 0
  have hex₃ : Exec w (.assign rBridgeLabel (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [checkWord])
  let I (i : ℕ) (st : State) : Prop :=
    st.regs rBridgeLabel = i ∧ st.arrs aBridgeAllowed = A.map Fin.val ∧
      st.arrs aLab = List.ofFn (bridgeLabels (A.take i))
  have hI₀ : I 0 s₃ := by
    refine ⟨by simp [s₃], hA₂, ?_⟩
    have hnil : bridgeLabels ([] : List (Fin n)) = fun _ => 2 := by
      funext v; simp [bridgeLabels]
    simpa [s₃, hnil, List.ofFn_const] using hlab₂
  have hloop : ⦃I 0⦄[w]
      forUp rBridgeLabel (.len aBridgeAllowed)
        (.write aLab (.read aBridgeAllowed (.reg rBridgeLabel)) (.const 0))
      ⦃I A.length⦄ ≤ fun _ => 3 + A.length * 11 := by
    apply Triple.forUp_const I A.length 4 (by omega) hlen
    · intro i _ st hi
      exact ⟨hi.1, by simp [Expr.eval, hi.2.1, checkWord, hlen]⟩
    · intro i hi st hI
      let u := A[i]'hi
      have hu : u.1 < 2 ^ w := lt_trans u.2 hn
      have he : (Expr.read aBridgeAllowed (.reg rBridgeLabel)).eval w st = some u.1 := by
        simp [Expr.eval, checkWord, hI.1, hI.2.1, hi, show i < 2 ^ w from lt_trans hi hlen, hu, u]
      let st' := st.writeArr aLab u.1 0
      have hex : Exec w (.write aLab (.read aBridgeAllowed (.reg rBridgeLabel)) (.const 0))
          st st' 4 := .write he (by simp [checkWord])
            (by rw [hI.2.2]; simp)
      refine ⟨st', 4, hex, le_rfl, ⟨?_, ?_⟩⟩
      · refine ⟨by simp, ?_, ?_⟩
        · simpa [st', State.writeArr] using hI.2.1
        · change (st.arrs aLab).set u.1 0 = List.ofFn (bridgeLabels (A.take (i + 1)))
          rw [hI.2.2, ofFn_set u, List.take_succ_eq_append_getElem hi, bridgeLabels_append]
      · exact hI.1
  obtain ⟨s₄, t₄, hex₄, ht₄, hI₄⟩ := hloop s₃ hI₀
  have hex : Exec w bridgeLabelProg s s₄ _ := .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, _, hex, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_replicate] at ht₂
    dsimp only at ht₄
    omega
  · simpa only [List.take_length] using hI₄.2.2
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [bridgeLabelProg, fillArr, forUp, Cmd.writtenRegs, hr])
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [bridgeLabelProg, fillArr, forUp, Cmd.writtenArrs, ha])

end GraphMinor.Compute
