module

public import GraphMinor.Compute.CrossingOpsReplPre
public import GraphMinor.Compute.CrossingOpsReplEncode
public import GraphMinor.Compute.CrossingOpsReplRebuild

/-!
# Arrays and registers written by the replacement phases

These membership formulas allow preservation proofs to use short lists instead of unfolding
all the nested loops each time.
-/

public section

namespace GraphMinor.Compute.Crossing

/-- The four phases before the alive-array update. -/
@[expose] def replacePrefixProg (a : InstArrs) (d b p rec rr A R : ℕ) : Cmd :=
  .seq (replPreProg a d b p A R) (.seq (replEncodeProg b p A R)
    (.seq (contrAppBuf rec rr A R) (replRebuildProg b a.st a.en a.ent A R)))

/-- The five phases of replacement, with records stored in a buffer. -/
@[expose] def replaceBufProg (a : InstArrs) (a_del a_bd a_rep a_rec r_rec A R : ℕ) : Cmd :=
  .seq (replPreProg a a_del a_bd a_rep A R)
    (.seq (replEncodeProg a_bd a_rep A R)
      (.seq (contrAppBuf a_rec r_rec A R)
        (.seq (replRebuildProg a_bd a.st a.en a.ent A R)
          (writeAllProg a.alive a_del 0 (R + 5) (R + 6) (R + 7)))))

local macro "footprint_simp" : tactic => `(tactic| simp [replPreProg,
  copyInstanceProg, copyMinProg, bArrs, InstArrs.list, markArrayProg, writeAllProg,
  concatProg, copyAtProg, replEncodeProg, replRecordBodyProg, replHeaderProg,
  emitFieldProg, emitArrayProg, emitPairsProg, emitPairListProg, emitMarkedPairProg,
  emitPairProg, patchPairCountProg, emitLengthProg, finishReplRecordProg,
  contrAppBuf, replRebuildProg, vertexLoopProg, replBody, emitSurvivingListProg,
  emitUnmarkedProg, emitBoundaryProg, emitMissingNeighbourProg, findNeighbourProg,
  forArrProg, forList, forUp, emitProg, copyMinNProg, Cmd.writtenArrs, Cmd.writtenRegs])

/-- The arrs written by the pre phase. -/
@[simp] theorem repl_pre_writtenArrs_mem (a : InstArrs) (d b p A R : ℕ) (x : ℕ) :
    x ∈ (replPreProg a d b p A R).writtenArrs ↔ x ∈ ((bArrs A).list ++ [A+3,A+9,A+11,A+10] : List ℕ) := by
  footprint_simp <;> simp [or_assoc, or_comm, or_left_comm]

/-- The regs written by the pre phase. -/
@[simp] theorem repl_pre_writtenRegs_mem (a : InstArrs) (d b p A R : ℕ) (x : ℕ) :
    x ∈ (replPreProg a d b p A R).writtenRegs ↔ x ∈ ([R+5,R+6,R+7,R+8,R+11,R+12,R+13,R+14,R+15,R+16,R+17] : List ℕ) := by
  footprint_simp <;> simp [or_assoc, or_comm, or_left_comm]

/-- The arrs written by the encode phase. -/
@[simp] theorem repl_encode_writtenArrs_mem (b p A R : ℕ) (x : ℕ) :
    x ∈ (replEncodeProg b p A R).writtenArrs ↔ x ∈ ([A+4,A+7] : List ℕ) := by
  footprint_simp <;> simp [or_assoc, or_comm, or_left_comm]

/-- The regs written by the encode phase. -/
@[simp] theorem repl_encode_writtenRegs_mem (b p A R : ℕ) (x : ℕ) :
    x ∈ (replEncodeProg b p A R).writtenRegs ↔ x ∈ ([R,R+1,R+2,R+3,R+4,R+5,R+6,R+9,R+10,R+11,R+12,R+14] : List ℕ) := by
  footprint_simp <;> simp [or_assoc, or_comm, or_left_comm]

/-- The arrs written by the append phase. -/
@[simp] theorem repl_append_writtenArrs_mem (a r A R : ℕ) (x : ℕ) :
    x ∈ (contrAppBuf a r A R).writtenArrs ↔ x ∈ ([a] : List ℕ) := by
  footprint_simp <;> simp [or_assoc, or_comm, or_left_comm]

/-- The regs written by the append phase. -/
@[simp] theorem repl_append_writtenRegs_mem (a r A R : ℕ) (x : ℕ) :
    x ∈ (contrAppBuf a r A R).writtenRegs ↔ x ∈ ([r,R+11,R+12,R+13,R+14] : List ℕ) := by
  footprint_simp <;> simp [or_assoc, or_comm, or_left_comm]

/-- The arrs written by the rebuild phase. -/
@[simp] theorem repl_rebuild_writtenArrs_mem (b st en ent A R : ℕ) (x : ℕ) :
    x ∈ (replRebuildProg b st en ent A R).writtenArrs ↔ x ∈ ([st,en,A+4,ent] : List ℕ) := by
  footprint_simp <;> simp [or_assoc, or_comm, or_left_comm]

/-- The regs written by the rebuild phase. -/
@[simp] theorem repl_rebuild_writtenRegs_mem (b st en ent A R : ℕ) (x : ℕ) :
    x ∈ (replRebuildProg b st en ent A R).writtenRegs ↔ x ∈ ([R,R+1,R+2,R+3,R+4,R+5,R+6,R+7,R+9,R+11,R+12,R+14] : List ℕ) := by
  footprint_simp <;> simp [or_assoc, or_comm, or_left_comm]


/-- The arrays written before the alive-array update. -/
@[simp] theorem replacePrefix_writtenArrs_mem (a : InstArrs) (d b p rec rr A R x : ℕ) :
    x ∈ (replacePrefixProg a d b p rec rr A R).writtenArrs ↔
    x ∈ ((bArrs A).list ++ [A+3,A+9,A+11,A+10,A+4,A+7,rec,a.st,a.en,a.ent] : List ℕ) := by
  simp [replacePrefixProg, Cmd.writtenArrs, or_assoc, or_comm, or_left_comm]

/-- The arrays written by all five phases. -/
@[simp] theorem replaceBuf_writtenArrs_mem (a : InstArrs) (d b p rec rr A R x : ℕ) :
    x ∈ (replaceBufProg a d b p rec rr A R).writtenArrs ↔
    x ∈ ((bArrs A).list ++ [A+3,A+9,A+11,A+10,A+4,A+7,rec,a.st,a.en,a.ent,a.alive] : List ℕ) := by
  simp [replaceBufProg, writeAllProg, forArrProg, forUp, Cmd.writtenArrs,
    or_assoc, or_comm, or_left_comm]

/-- The registers written by all five phases. -/
@[simp] theorem replaceBuf_writtenRegs_mem (a : InstArrs) (d b p rec rr A R x : ℕ) :
    x ∈ (replaceBufProg a d b p rec rr A R).writtenRegs ↔
    x ∈ ([rr,R,R+1,R+2,R+3,R+4,R+5,R+6,R+7,R+8,R+9,R+10,R+11,R+12,R+13,R+14,R+15,R+16,R+17] : List ℕ) := by
  change (x ∈ ((replPreProg a d b p A R).writtenRegs ∪
    ((replEncodeProg b p A R).writtenRegs ∪
      ((contrAppBuf rec rr A R).writtenRegs ∪
        ((replRebuildProg b a.st a.en a.ent A R).writtenRegs ∪
          (writeAllProg a.alive d 0 (R+5) (R+6) (R+7)).writtenRegs))))) ↔ _
  simp only [Finset.mem_union]
  rw [repl_pre_writtenRegs_mem, repl_encode_writtenRegs_mem, repl_append_writtenRegs_mem,
    repl_rebuild_writtenRegs_mem]
  simp [writeAllProg, forArrProg, forUp, Cmd.writtenRegs] <;> tauto

/-- An execution preserves every array outside the listed writes. -/
theorem repl_pre_arrs_eq {w : ℕ} (a : InstArrs) (d b p A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replPreProg a d b p A R) s s' t) (hx : x ∉ ((bArrs A).list ++ [A+3,A+9,A+11,A+10] : List ℕ)) :
    s'.arrs x = s.arrs x :=
  h.arrs_eq_of_not_mem_writtenArrs
    ((not_congr (repl_pre_writtenArrs_mem a d b p A R x)).mpr hx)

/-- An execution preserves every register outside the listed writes. -/
theorem repl_pre_regs_eq {w : ℕ} (a : InstArrs) (d b p A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replPreProg a d b p A R) s s' t) (hx : x ∉ ([R+5,R+6,R+7,R+8,R+11,R+12,R+13,R+14,R+15,R+16,R+17] : List ℕ)) :
    s'.regs x = s.regs x :=
  h.regs_eq_of_not_mem_writtenRegs
    ((not_congr (repl_pre_writtenRegs_mem a d b p A R x)).mpr hx)

/-- An execution preserves every array outside the listed writes. -/
theorem repl_encode_arrs_eq {w : ℕ} (b p A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replEncodeProg b p A R) s s' t) (hx : x ∉ ([A+4,A+7] : List ℕ)) :
    s'.arrs x = s.arrs x :=
  h.arrs_eq_of_not_mem_writtenArrs
    ((not_congr (repl_encode_writtenArrs_mem b p A R x)).mpr hx)

/-- An execution preserves every register outside the listed writes. -/
theorem repl_encode_regs_eq {w : ℕ} (b p A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replEncodeProg b p A R) s s' t) (hx : x ∉ ([R,R+1,R+2,R+3,R+4,R+5,R+6,R+9,R+10,R+11,R+12,R+14] : List ℕ)) :
    s'.regs x = s.regs x :=
  h.regs_eq_of_not_mem_writtenRegs
    ((not_congr (repl_encode_writtenRegs_mem b p A R x)).mpr hx)

/-- An execution preserves every array outside the listed writes. -/
theorem repl_append_arrs_eq {w : ℕ} (a r A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (contrAppBuf a r A R) s s' t) (hx : x ∉ ([a] : List ℕ)) :
    s'.arrs x = s.arrs x :=
  h.arrs_eq_of_not_mem_writtenArrs
    ((not_congr (repl_append_writtenArrs_mem a r A R x)).mpr hx)

/-- An execution preserves every register outside the listed writes. -/
theorem repl_append_regs_eq {w : ℕ} (a r A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (contrAppBuf a r A R) s s' t) (hx : x ∉ ([r,R+11,R+12,R+13,R+14] : List ℕ)) :
    s'.regs x = s.regs x :=
  h.regs_eq_of_not_mem_writtenRegs
    ((not_congr (repl_append_writtenRegs_mem a r A R x)).mpr hx)

/-- An execution preserves every array outside the listed writes. -/
theorem repl_rebuild_arrs_eq {w : ℕ} (b st en ent A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replRebuildProg b st en ent A R) s s' t) (hx : x ∉ ([st,en,A+4,ent] : List ℕ)) :
    s'.arrs x = s.arrs x :=
  h.arrs_eq_of_not_mem_writtenArrs
    ((not_congr (repl_rebuild_writtenArrs_mem b st en ent A R x)).mpr hx)

/-- An execution preserves every register outside the listed writes. -/
theorem repl_rebuild_regs_eq {w : ℕ} (b st en ent A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replRebuildProg b st en ent A R) s s' t) (hx : x ∉ ([R,R+1,R+2,R+3,R+4,R+5,R+6,R+7,R+9,R+11,R+12,R+14] : List ℕ)) :
    s'.regs x = s.regs x :=
  h.regs_eq_of_not_mem_writtenRegs
    ((not_congr (repl_rebuild_writtenRegs_mem b st en ent A R x)).mpr hx)

/-- An execution preserves every array outside the listed writes. -/
theorem replacePrefix_arrs_eq {w : ℕ} (a : InstArrs) (d b p rec rr A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replacePrefixProg a d b p rec rr A R) s s' t) (hx : x ∉ ((bArrs A).list ++ [A+3,A+9,A+11,A+10,A+4,A+7,rec,a.st,a.en,a.ent] : List ℕ)) :
    s'.arrs x = s.arrs x :=
  h.arrs_eq_of_not_mem_writtenArrs
    ((not_congr (replacePrefix_writtenArrs_mem a d b p rec rr A R x)).mpr hx)

/-- An execution preserves every array outside the listed writes. -/
theorem replaceBuf_arrs_eq {w : ℕ} (a : InstArrs) (d b p rec rr A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replaceBufProg a d b p rec rr A R) s s' t) (hx : x ∉ ((bArrs A).list ++ [A+3,A+9,A+11,A+10,A+4,A+7,rec,a.st,a.en,a.ent,a.alive] : List ℕ)) :
    s'.arrs x = s.arrs x :=
  h.arrs_eq_of_not_mem_writtenArrs
    ((not_congr (replaceBuf_writtenArrs_mem a d b p rec rr A R x)).mpr hx)

/-- An execution preserves every register outside the listed writes. -/
theorem replaceBuf_regs_eq {w : ℕ} (a : InstArrs) (d b p rec rr A R : ℕ) {s s' : State} {t x : ℕ}
    (h : Exec w (replaceBufProg a d b p rec rr A R) s s' t) (hx : x ∉ ([rr,R,R+1,R+2,R+3,R+4,R+5,R+6,R+7,R+8,R+9,R+10,R+11,R+12,R+13,R+14,R+15,R+16,R+17] : List ℕ)) :
    s'.regs x = s.regs x :=
  h.regs_eq_of_not_mem_writtenRegs
    ((not_congr (replaceBuf_writtenRegs_mem a d b p rec rr A R x)).mpr hx)

/-- Below the scratch base, only the record and rebuilt graph arrays change in the prefix. -/
theorem replacePrefix_arrs_eq_of_lt {w : ℕ} (a : InstArrs) (d b p rec rr A R : ℕ)
    {s s' : State} {t x : ℕ} (h : Exec w (replacePrefixProg a d b p rec rr A R) s s' t)
    (hx : x < A) (hst : x ≠ a.st) (hen : x ≠ a.en) (hent : x ≠ a.ent) (hrec : x ≠ rec) :
    s'.arrs x = s.arrs x := by
  apply replacePrefix_arrs_eq a d b p rec rr A R h
  simp only [bArrs, InstArrs.list, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or]
  omega

/-- The full program preserves all caller arrays and registers outside its interface outputs. -/
theorem replaceBuf_keeps {w : ℕ} (a : InstArrs) (d b p rec rr A R : ℕ)
    {s s' : State} {t : ℕ} (h : Exec w (replaceBufProg a d b p rec rr A R) s s' t) :
    KeepsBelow R A [rr] (a.list ++ [rec]) s s' := by
  constructor
  · intro q hq hqr
    apply replaceBuf_regs_eq a d b p rec rr A R h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [List.mem_singleton] at hqr
    omega
  · intro x hx hxl
    apply replaceBuf_arrs_eq a d b p rec rr A R h
    simp only [bArrs, InstArrs.list, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    simp only [InstArrs.list, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.mem_singleton] at hxl
    omega

/-- Below the scratch base, rebuilding changes only the three graph arrays. -/
theorem repl_rebuild_arrs_eq_of_lt {w : ℕ} (b st en ent A R : ℕ)
    {s s' : State} {t x : ℕ} (h : Exec w (replRebuildProg b st en ent A R) s s' t)
    (hx : x < A) (hst : x ≠ st) (hen : x ≠ en) (hent : x ≠ ent) :
    s'.arrs x = s.arrs x := by
  apply repl_rebuild_arrs_eq b st en ent A R h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  omega

/-- Rebuilding uses only scratch registers. -/
theorem repl_rebuild_regs_eq_of_lt {w : ℕ} (b st en ent A R : ℕ)
    {s s' : State} {t x : ℕ} (h : Exec w (replRebuildProg b st en ent A R) s s' t)
    (hx : x < R) : s'.regs x = s.regs x := by
  apply repl_rebuild_regs_eq b st en ent A R h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  omega

end GraphMinor.Compute.Crossing
