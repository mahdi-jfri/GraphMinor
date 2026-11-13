module

public import GraphMinor.Compute.CrossingLiftRead
public import GraphMinor.Compute.CrossingLiftReadSlice
import GraphMinor.Compute.TwoPathsFrameEdges

/-!
# The three lists stored in a replacement record

The replacement encoding stores a boundary list, a recorded component list and the ordered
old-edge pairs, each preceded by its length. This file gives their runtime offsets and the
exact list data. The loader reads each slice into a separate scratch array, retaining the
record buffer and the caller's lower registers.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The body of the replacement encoding, in the order used by `IsRecordEnc`. -/
def liftReplacementBody {N : ℕ} (B C : List (Fin N)) (E : List (Fin N × Fin N)) : List ℕ :=
  [0, B.length] ++ B.map Fin.val ++ [C.length] ++ C.map Fin.val ++ [E.length] ++ E.flatMap encPair

/-- Position of the recorded-component length field after the boundary list. -/
def liftReplComponentPos (boundary r_start : ℕ) : Expr :=
  .op .add (.op .add (.reg r_start) (.const 2)) (.len boundary)

/-- Position of the edge-count field after the boundary and component lists. -/
def liftReplEdgesPos (boundary component r_start : ℕ) : Expr :=
  .op .add (.op .add (.op .add (.reg r_start) (.const 3)) (.len boundary)) (.len component)

/-- Load the boundary, recorded component and flat ordered-edge pairs at the known record start. -/
def liftLoadReplacementProg (a_rec boundary component edges r_start R : ℕ) : Cmd :=
  .seq (liftReadSliceProg a_rec boundary (.op .add (.reg r_start) (.const 2))
      (.read a_rec (.op .add (.reg r_start) (.const 1))) R)
    (.seq (liftReadSliceProg a_rec component
        (.op .add (liftReplComponentPos boundary r_start) (.const 1))
        (.read a_rec (liftReplComponentPos boundary r_start)) R)
      (liftReadSliceProg a_rec edges
        (.op .add (liftReplEdgesPos boundary component r_start) (.const 1))
        (.op .mul (.const 2) (.read a_rec (liftReplEdgesPos boundary component r_start))) R))

private theorem pair_words_length {N : ℕ} (E : List (Fin N × Fin N)) :
    (E.flatMap encPair).length = 2 * E.length := TwoPaths.length_pairsList E

private theorem field_after_prefix (P T : List ℕ) (v i : ℕ) (hi : i = P.length) :
    (P ++ v :: T)[i]? = some v := by
  rw [hi, List.getElem?_append_right (by omega)]
  simp

/-- The record body's three length fields can be read at their computed positions. -/
theorem liftReplacementBody_fields {N : ℕ} (B C : List (Fin N)) (E : List (Fin N × Fin N)) :
    (liftReplacementBody B C E)[1]? = some B.length ∧
    (liftReplacementBody B C E)[2 + B.length]? = some C.length ∧
    (liftReplacementBody B C E)[3 + B.length + C.length]? = some E.length := by
  refine ⟨by simp [liftReplacementBody], ?_, ?_⟩
  · have hb : liftReplacementBody B C E = ([0, B.length] ++ B.map Fin.val) ++
        C.length :: (C.map Fin.val ++ E.length :: E.flatMap encPair) := by
      simp only [liftReplacementBody, List.append_assoc, List.cons_append, List.nil_append]
    rw [hb]
    exact field_after_prefix _ _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil, List.length_map])
  · have hb : liftReplacementBody B C E =
        ([0, B.length] ++ B.map Fin.val ++ [C.length] ++ C.map Fin.val) ++
          E.length :: E.flatMap encPair := by
      simp only [liftReplacementBody, List.append_assoc, List.cons_append, List.nil_append]
    rw [hb]
    exact field_after_prefix _ _ _ _ (by simp only [List.length_append, List.length_map,
      List.length_cons, List.length_nil]; omega)

/-- The length of the body pays for all three list copies. -/
theorem liftReplacementBody_length {N : ℕ} (B C : List (Fin N)) (E : List (Fin N × Fin N)) :
    (liftReplacementBody B C E).length = B.length + C.length + 2 * E.length + 4 := by
  simp only [liftReplacementBody, List.length_append, List.length_map, List.length_cons,
    List.length_nil, pair_words_length]
  omega

private theorem replacement_array_layout (a_rec boundary component edges : ℕ)
    (h : [a_rec, boundary, component, edges].Nodup) :
    a_rec ≠ boundary ∧ a_rec ≠ component ∧ a_rec ≠ edges ∧
      boundary ≠ component ∧ boundary ≠ edges ∧ component ≠ edges := by
  simpa only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true, and_assoc] using h

/-- The replacement loader decodes all three lists in linear time. No validity or graph
hypothesis is needed: the exact record encoding and word/layout bounds suffice. -/
theorem liftLoadReplacementProg_exec {w N : ℕ} (B C : List (Fin N)) (E : List (Fin N × Fin N))
    (a_rec boundary component edges r_start R : ℕ)
    (harr : [a_rec, boundary, component, edges].Nodup) (hsR : r_start < R)
    (pre spare : List ℕ) (s : State)
    (hrec : s.arrs a_rec = pre ++ withLength (liftReplacementBody B C E) ++ spare)
    (hstart : s.regs r_start = pre.length)
    (hw : N + pre.length + B.length + C.length + 2 * E.length + 16 < 2 ^ w) :
    ∃ s' t, Exec w (liftLoadReplacementProg a_rec boundary component edges r_start R) s s' t ∧
      t ≤ 30 * (B.length + C.length + 2 * E.length + 1) + 100 ∧
      s'.arrs boundary = B.map Fin.val ∧ s'.arrs component = C.map Fin.val ∧
      s'.arrs edges = E.flatMap encPair ∧
      (∀ a, a ∉ [boundary, component, edges] → s'.arrs a = s.arrs a) ∧
      (∀ q < R, s'.regs q = s.regs q) := by
  obtain ⟨hrb, hrc, hre, hbc, hbe, hce⟩ := replacement_array_layout a_rec boundary component edges harr
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  let body := liftReplacementBody B C E
  let tail := [body.length] ++ spare
  have hflat : s.arrs a_rec = pre ++ body ++ tail := by
    simpa only [withLength, body, tail, List.append_assoc] using hrec
  have fields := liftReplacementBody_fields B C E
  have hBlen : (B.map Fin.val).length = B.length := List.length_map Fin.val
  have hClen : (C.map Fin.val).length = C.length := List.length_map Fin.val
  have hfield : ∀ st : State, st.arrs a_rec = s.arrs a_rec → st.regs r_start = pre.length →
      ∀ i v, body[i]? = some v → v < 2 ^ w →
      (Expr.read a_rec (.op .add (.reg r_start) (.const i))).eval w st = some v := by
    intro st ha hs i v hv hvw
    exact eval_lift_record_field (ha.trans hflat) hs hv hvw
      (by dsimp [body]; rw [liftReplacementBody_length]; omega)
  have hmapword : ∀ xs : List (Fin N), ∀ x ∈ xs.map Fin.val, x < 2 ^ w := by
    intro xs x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.isLt.trans (by omega)
  have hedgeword : ∀ x ∈ E.flatMap encPair, x < 2 ^ w := by
    intro x hx
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hx
    simp only [encPair, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact p.1.isLt.trans (by omega)
    · exact p.2.isLt.trans (by omega)
  have hsliceB : s.arrs a_rec = (pre ++ [0, B.length]) ++ B.map Fin.val ++
      (C.length :: C.map Fin.val ++ E.length :: E.flatMap encPair ++ tail) := by
    simpa only [body, liftReplacementBody, List.append_assoc, List.cons_append, List.nil_append] using hflat
  obtain ⟨s1, t1, he1, ht1, ho1, ha1, hr1⟩ := liftReadSliceProg_exec
    a_rec boundary R (.op .add (.reg r_start) (.const 2))
    (.read a_rec (.op .add (.reg r_start) (.const 1))) hrb
    (pre ++ [0, B.length]) (B.map Fin.val)
    (C.length :: C.map Fin.val ++ E.length :: E.flatMap encPair ++ tail) s hsliceB
    (by simpa only [List.length_map] using hfield s rfl hstart 1 B.length fields.1 (by omega))
    (by
      have he := eval_add (w := w) (s := s.setArr boundary (List.replicate (B.map Fin.val).length 0))
        (eval_reg hstart (by omega)) (eval_const hw2) (by omega)
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd] using he)
    (hmapword B) (by simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]; omega)
  have hrec1 : s1.arrs a_rec = s.arrs a_rec := ha1 a_rec hrb
  have hstart1 : s1.regs r_start = pre.length := (hr1 r_start hsR).trans hstart
  have hsliceC : s1.arrs a_rec =
      (pre ++ [0, B.length] ++ B.map Fin.val ++ [C.length]) ++ C.map Fin.val ++
        (E.length :: E.flatMap encPair ++ tail) := by
    rw [hrec1]
    simpa only [body, liftReplacementBody, List.append_assoc, List.cons_append, List.nil_append] using hflat
  have hposC : (liftReplComponentPos boundary r_start).eval w s1 = some (pre.length + (2 + B.length)) := by
    have he := eval_add (w := w) (eval_add (eval_reg hstart1 (by omega)) (eval_const hw2) (by omega))
      (eval_len ho1 (by omega)) (by omega)
    simpa only [liftReplComponentPos, List.length_map, Nat.add_assoc] using he
  have hcountC : (Expr.read a_rec (liftReplComponentPos boundary r_start)).eval w s1 = some C.length := by
    have hvalue : (s1.arrs a_rec)[pre.length + (2 + B.length)]? = some C.length := by
      have hs := hrec1.trans hflat
      have hbody := fields.2.1
      rw [hs, List.getElem?_append_left (by simp only [List.length_append]; dsimp [body]; rw [liftReplacementBody_length]; omega),
        List.getElem?_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left] using hbody
    obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hvalue
    rw [← hv]
    exact eval_read hposC hi (by rw [hv]; omega)
  obtain ⟨s2, t2, he2, ht2, ho2, ha2, hr2⟩ := liftReadSliceProg_exec
    a_rec component R (.op .add (liftReplComponentPos boundary r_start) (.const 1))
    (.read a_rec (liftReplComponentPos boundary r_start)) hrc
    (pre ++ [0, B.length] ++ B.map Fin.val ++ [C.length]) (C.map Fin.val)
    (E.length :: E.flatMap encPair ++ tail) s1 hsliceC
    (by simpa only [List.length_map] using hcountC)
    (by
      have hp : (liftReplComponentPos boundary r_start).eval w
          (s1.setArr component (List.replicate (C.map Fin.val).length 0)) = some (pre.length + (2 + B.length)) := by
        unfold liftReplComponentPos
        have he := eval_add (w := w)
          (s := s1.setArr component (List.replicate (C.map Fin.val).length 0))
          (eval_add (eval_reg hstart1 (by omega)) (eval_const hw2) (by omega))
          (eval_len (a := boundary) (L := B.map Fin.val)
            ((State.setArr_arrs_ne _ _ hbc).trans ho1) (by omega)) (by omega)
        simpa only [List.length_map, Nat.add_assoc] using he
      have he := eval_add hp (eval_const hw1) (by omega)
      convert he using 1
      congr 1
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      omega)
    (hmapword C) (by simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]; omega)
  have hrec2 : s2.arrs a_rec = s.arrs a_rec := (ha2 a_rec hrc).trans hrec1
  have hstart2 : s2.regs r_start = pre.length := (hr2 r_start hsR).trans hstart1
  have hbd2 : s2.arrs boundary = B.map Fin.val := (ha2 boundary hbc).trans ho1
  have hsliceE : s2.arrs a_rec =
      (pre ++ [0, B.length] ++ B.map Fin.val ++ [C.length] ++ C.map Fin.val ++ [E.length]) ++
        E.flatMap encPair ++ tail := by
    rw [hrec2]
    simpa only [body, liftReplacementBody, List.append_assoc] using hflat
  have hposE : (liftReplEdgesPos boundary component r_start).eval w s2 =
      some (pre.length + (3 + B.length + C.length)) := by
    unfold liftReplEdgesPos
    have he := eval_add (w := w) (eval_add (eval_add (eval_reg hstart2 (by omega)) (eval_const (c := 3) (by omega)) (by omega))
      (eval_len hbd2 (by simp only [List.length_map]; omega)) (by omega))
      (eval_len ho2 (by simp only [List.length_map]; omega)) (by omega)
    simpa only [List.length_map, Nat.add_assoc] using he
  have hcountE : (Expr.read a_rec (liftReplEdgesPos boundary component r_start)).eval w s2 = some E.length := by
    have hvalue : (s2.arrs a_rec)[pre.length + (3 + B.length + C.length)]? = some E.length := by
      rw [hrec2, hflat, List.getElem?_append_left (by simp only [List.length_append]; dsimp [body]; rw [liftReplacementBody_length]; omega),
        List.getElem?_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left] using fields.2.2
    obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hvalue
    rw [← hv]
    exact eval_read hposE hi (by rw [hv]; omega)
  obtain ⟨s3, t3, he3, ht3, ho3, ha3, hr3⟩ := liftReadSliceProg_exec
    a_rec edges R (.op .add (liftReplEdgesPos boundary component r_start) (.const 1))
    (.op .mul (.const 2) (.read a_rec (liftReplEdgesPos boundary component r_start))) hre
    (pre ++ [0, B.length] ++ B.map Fin.val ++ [C.length] ++ C.map Fin.val ++ [E.length])
    (E.flatMap encPair) tail s2 hsliceE
    (by simpa only [pair_words_length] using eval_mul (eval_const hw2) hcountE (by omega))
    (by
      have hp : (liftReplEdgesPos boundary component r_start).eval w
          (s2.setArr edges (List.replicate (E.flatMap encPair).length 0)) =
          some (pre.length + (3 + B.length + C.length)) := by
        unfold liftReplEdgesPos
        have he := eval_add (w := w)
          (s := s2.setArr edges (List.replicate (E.flatMap encPair).length 0))
          (eval_add (eval_add (eval_reg hstart2 (by omega)) (eval_const (c := 3) (by omega)) (by omega))
            (eval_len (a := boundary) (L := B.map Fin.val)
              ((State.setArr_arrs_ne _ _ hbe).trans hbd2) (by simp only [List.length_map]; omega)) (by omega))
          (eval_len (a := component) (L := C.map Fin.val)
            ((State.setArr_arrs_ne _ _ hce).trans ho2) (by simp only [List.length_map]; omega)) (by omega)
        simpa only [List.length_map, Nat.add_assoc] using he
      have he := eval_add hp (eval_const hw1) (by omega)
      convert he using 1
      congr 1
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      omega)
    hedgeword (by simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, pair_words_length]; omega)
  refine ⟨s3, t1 + (t2 + t3), .seq he1 (.seq he2 he3), ?_,
    (ha3 boundary hbe).trans hbd2, (ha3 component hce).trans ho2, ho3, ?_, ?_⟩
  · simp only [Expr.cost, liftReplComponentPos, liftReplEdgesPos, List.length_map, pair_words_length] at ht1 ht2 ht3
    omega
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at ha
    exact (ha3 a ha.2.2).trans ((ha2 a ha.2.1).trans (ha1 a ha.1))
  · intro q hq; exact (hr3 q hq).trans ((hr2 q hq).trans (hr1 q hq))

end GraphMinor.Compute.Crossing
