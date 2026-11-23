import DiagonalReturnOrder
import DiagonalWinding
import RootWord

/-!
# Physical upper segments and their timing

This file develops the physical interfaces used in rounds 21, 23--24 and
the east-entry parity observation of round 32 of
`research/persist-B-diagonal-m3-2026-11-22.md`.

An excursion includes its two boundary events. Its strictly interior events
form a maximal run above the boundary. Adjacent excursions can share one
boundary event; this convention is essential for splicing parent segments.
All times and displacements below are lifted physical quantities.
-/

namespace LangtonsAnt.DiagonalSegments

open DiagonalMultipleLanes

def time {P len : Nat} (p : ContinuousPhasePath P len) (r : Nat) : Int :=
  p.period r * (P : Int) + p.phase r

theorem time_eq {P len : Nat} (p : ContinuousPhasePath P len) {r : Nat}
    (hr : r <= len) : time p r = time p 0 + (r : Int) := p.time_eq hr

theorem pos_eq_of_time_eq {P a b i j : Nat}
    (p : ContinuousPhasePath P a) (q : ContinuousPhasePath P b)
    (hi : i <= a) (hj : j <= b) (ht : time p i = time q j) (w : Nat -> Bool) :
    p.pos w i = q.pos w j := by
  obtain ⟨hp, hf⟩ := biTime_injective (p.phase_lt i hi) (q.phase_lt j hj) ht
  simp only [ContinuousPhasePath.pos, hp, hf]

/-- A whole-period translate of the same physical path. -/
def copy {P len : Nat} (p : ContinuousPhasePath P len) (z : Int) :
    ContinuousPhasePath P len where
  phase := p.phase
  period r := p.period r + z
  phase_lt := p.phase_lt
  time_step r hr := by
    have h := p.time_step r hr
    simp only [Int.add_mul]
    omega

theorem time_copy {P len : Nat} (p : ContinuousPhasePath P len) (z : Int) (r : Nat) :
    time (copy p z) r = time p r + z * (P : Int) := by
  simp only [time, copy, Int.add_mul]
  omega

theorem pos_copy {P len : Nat} (p : ContinuousPhasePath P len)
    (w : Nat -> Bool) (z : Int) (r : Nat) :
    (copy p z).pos w r = addPoint (p.pos w r) (scalePoint (wordDrift P w) z) := by
  apply Prod.ext <;>
    simp only [ContinuousPhasePath.pos, copy, biPeriodicPos, addPoint, scalePoint,
      Int.add_mul] <;> omega

/-- Restriction to a closed time interval, retaining the actual period carry. -/
def slice {P len : Nat} (p : ContinuousPhasePath P len) (start size : Nat)
    (h : start + size <= len) : ContinuousPhasePath P size where
  phase r := p.phase (start + r)
  period r := p.period (start + r)
  phase_lt r hr := p.phase_lt _ (by omega)
  time_step r hr := by
    have hh := p.time_step (start + r) (by omega)
    simpa only [Nat.add_assoc] using hh

/-- Concatenation identifies the common boundary event, with no time gap. -/
def splice {P a b : Nat} (p : ContinuousPhasePath P a) (q : ContinuousPhasePath P b)
    (h : time p a = time q 0) : ContinuousPhasePath P (a + b) where
  phase r := if r <= a then p.phase r else q.phase (r - a)
  period r := if r <= a then p.period r else q.period (r - a)
  phase_lt r hr := by
    split
    · exact p.phase_lt r (by omega)
    · exact q.phase_lt (r - a) (by omega)
  time_step r hr := by
    by_cases hl : r < a
    · simp only [ite_eq_left (show r + 1 <= a by omega), ite_eq_left (show r <= a by omega)]
      exact p.time_step r hl
    · by_cases he : r = a
      · subst r
        simp only [ite_eq_right (show ¬a + 1 <= a by omega), ite_eq_left (Nat.le_refl a)]
        have hh := q.time_step 0 (show 0 < b by omega)
        have hn : a + 1 - a = 1 := by omega
        rw [hn]
        change _ = time p a + 1
        rw [h]
        exact hh
      · simp only [ite_eq_right (show ¬r + 1 <= a by omega),
          ite_eq_right (show ¬r <= a by omega)]
        have hh := q.time_step (r - a) (by omega)
        have hn : r + 1 - a = (r - a) + 1 := by omega
        rw [hn]
        exact hh

theorem splice_pos_left {P a b : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) (h : time p a = time q 0)
    (w : Nat -> Bool) {r : Nat} (hr : r <= a) :
    (splice p q h).pos w r = p.pos w r := by
  simp only [ContinuousPhasePath.pos, splice, ite_eq_left hr]

theorem splice_pos_right {P a b : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) (h : time p a = time q 0)
    (w : Nat -> Bool) {r : Nat} (hr : r <= b) :
    (splice p q h).pos w (a + r) = q.pos w r := by
  by_cases hz : r = 0
  · subst r
    simpa only [Nat.add_zero, splice_pos_left p q h w (Nat.le_refl a)] using
      pos_eq_of_time_eq p q (Nat.le_refl a) (by omega) h w
  · simp only [ContinuousPhasePath.pos, splice,
      ite_eq_right (show ¬a + r <= a by omega), Nat.add_sub_cancel_left]

theorem time_splice_start {P a b : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) (h : time p a = time q 0) :
    time (splice p q h) 0 = time p 0 := by
  simp only [time, splice, Nat.zero_le, ite_true]

theorem time_splice_end {P a b : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) (h : time p a = time q 0) :
    time (splice p q h) (a + b) = time q b := by
  rw [time_eq (splice p q h) (Nat.le_refl _), time_splice_start,
    time_eq q (Nat.le_refl _)]
  have hh := time_eq p (Nat.le_refl _)
  omega

/-- Physical blocks may meet at their common boundary event. -/
def Separated {P a b : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) : Prop :=
  time p a <= time q 0 ∨ time q b <= time p 0

/-- A third nonempty block cannot lie in the join of two spliced blocks.
This is the persistence fact for every partial bridge contraction in round 24. -/
theorem splice_separated {P a b c : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) (r : ContinuousPhasePath P c)
    (h : time p a = time q 0) (hc : 0 < c)
    (hp : Separated p r) (hq : Separated q r) : Separated (splice p q h) r := by
  unfold Separated at hp hq ⊢
  rw [time_splice_start, time_splice_end]
  have ht := time_eq r (Nat.le_refl _)
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact Or.inl hq
  · omega
  · exact Or.inr hp
  · exact Or.inr hp

theorem separated_slices {P a b : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) (h : Separated p q)
    (i n j m : Nat) (hi : i + n <= a) (hj : j + m <= b) :
    Separated (slice p i n hi) (slice q j m hj) := by
  unfold Separated at h ⊢
  change time p (i + n) <= time q (j + 0) ∨ time q (j + m) <= time p (i + 0)
  simp only [Nat.add_zero]
  rw [time_eq p hi, time_eq q (show j <= b by omega), time_eq q hj,
    time_eq p (show i <= a by omega)]
  rw [time_eq p (Nat.le_refl _), time_eq q (Nat.le_refl _)] at h
  rcases h with h | h <;> omega

def CopiesSeparated {P a b : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) : Prop := ∀ z u : Int, Separated (copy p z) (copy q u)

theorem copiesSeparated_splice {P a b c : Nat} (p : ContinuousPhasePath P a)
    (q : ContinuousPhasePath P b) (r : ContinuousPhasePath P c)
    (h : time p a = time q 0) (hc : 0 < c)
    (hp : CopiesSeparated p r) (hq : CopiesSeparated q r) :
    CopiesSeparated (splice p q h) r := by
  intro z u
  have hh : time (copy p z) a = time (copy q z) 0 := by rw [time_copy, time_copy, h]
  have hs := splice_separated (copy p z) (copy q z) (copy r u) hh hc (hp z u) (hq z u)
  unfold Separated at hs ⊢
  simp only [time_copy, time_splice_start, time_splice_end] at hs ⊢
  exact hs

/-- Maximal upper run, including its lower boundary endpoints. -/
structure Excursion (P : Nat) (w : Nat -> Bool) (L : Int) where
  len : Nat
  path : ContinuousPhasePath P len
  nonempty : 1 < len
  start_layer : layer (path.pos w 0) = L
  end_layer : layer (path.pos w len) = L
  above : ∀ r, 0 < r -> r < len -> L < layer (path.pos w r)

namespace Excursion

def start {P : Nat} {w : Nat -> Bool} {L : Int} (s : Excursion P w L) : Int :=
  time s.path 0

def finish {P : Nat} {w : Nat -> Bool} {L : Int} (s : Excursion P w L) : Int :=
  time s.path s.len

theorem finish_eq {P : Nat} {w : Nat -> Bool} {L : Int} (s : Excursion P w L) :
    s.finish = s.start + (s.len : Int) := time_eq s.path (Nat.le_refl _)

/-- Boundary separation proves disjoint interiors; no table-order assumption. -/
theorem finish_le_start {P : Nat} {w : Nat -> Bool} {L : Int}
    (s t : Excursion P w L) (h : s.start < t.start) : s.finish <= t.start := by
  by_cases hn : s.finish <= t.start
  · exact hn
  exfalso
  let r := (t.start - s.start).toNat
  have hr : (r : Int) = t.start - s.start := by dsimp [r]; omega
  have hf := s.finish_eq
  have hp : time s.path r = time t.path 0 := by
    rw [time_eq s.path (show r <= s.len by omega)]
    change s.start + (r : Int) = t.start
    omega
  have he := pos_eq_of_time_eq s.path t.path (by omega) (by omega) hp w
  have ha := s.above r (by omega) (by omega)
  rw [he, t.start_layer] at ha
  omega

theorem same_start_same_len {P : Nat} {w : Nat -> Bool} {L : Int}
    (s t : Excursion P w L) (h : s.start = t.start) : s.len = t.len := by
  have not_lt (a b : Excursion P w L) (he : a.start = b.start) : ¬a.len < b.len := by
    intro hl
    have ht : time b.path a.len = time a.path a.len := by
      rw [time_eq b.path (by omega), time_eq a.path (by omega)]
      change b.start + _ = a.start + _
      rw [he]
    have hp := pos_eq_of_time_eq b.path a.path (by omega) (by omega) ht w
    have ha := b.above a.len (by have := a.nonempty; omega) hl
    rw [hp, a.end_layer] at ha
    omega
  have := not_lt s t h
  have := not_lt t s h.symm
  omega

def translate {P : Nat} {w : Nat -> Bool} {L : Int} (s : Excursion P w L)
    (z : Int) (hd : layer (wordDrift P w) = 0) : Excursion P w L where
  len := s.len
  path := copy s.path z
  nonempty := s.nonempty
  start_layer := by
    rw [pos_copy]
    have hh := congrArg (fun x : Int => z * x) hd
    simp only [layer, weight, Int.mul_add, Int.mul_zero] at hh
    have ha := s.start_layer
    simp only [layer, weight, addPoint, scalePoint] at ha ⊢
    omega
  end_layer := by
    rw [pos_copy]
    have he : layer (addPoint (s.path.pos w s.len) (scalePoint (wordDrift P w) z)) =
        layer (s.path.pos w s.len) := by
      simp only [layer, weight, addPoint, scalePoint] at hd ⊢
      have hh := congrArg (fun x : Int => z * x) hd
      simp only [Int.mul_add, Int.mul_zero] at hh
      omega
    rw [he, s.end_layer]
  above r hr hrl := by
    rw [pos_copy]
    have hh := congrArg (fun x : Int => z * x) hd
    simp only [layer, weight, Int.mul_add, Int.mul_zero] at hh
    have ha := s.above r hr hrl
    simp only [layer, weight, addPoint, scalePoint] at ha ⊢
    omega

end Excursion

/-- Lift of an event relative to the canonical start of its segment. -/
def eventLift {P len : Nat} (p : ContinuousPhasePath P len) (w : Nat -> Bool)
    (r : Nat) : Int :=
  Drift.lift (wordDrift P w) (p.pos w r) - Drift.lift (wordDrift P w) (p.pos w 0)

def canonicalStart {P len : Nat} (p : ContinuousPhasePath P len) (w : Nat -> Bool) : Int :=
  time p 0 - (P : Int) * Drift.lift (wordDrift P w) (p.pos w 0)

theorem stableTime_event {P len : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P len) (hv : wordDrift P w ≠ (0, 0)) {r : Nat}
    (hr : r <= len) :
    Drift.stableTime (wordDrift P w) P w (p.phase r) =
      canonicalStart p w + (r : Int) - (P : Int) * eventLift p w r := by
  rw [Drift.path_stableTime_eq p rfl hv r]
  change time p r - _ = _
  rw [time_eq p hr]
  simp only [canonicalStart, eventLift, Int.mul_sub]
  omega

/-- Rank comparison for arbitrary physical blocks whose lifted copies are
separated. The property is preserved by every actual no-gap splice. -/
theorem blocks_rank_edge {P a b i j : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P a) (q : ContinuousPhasePath P b)
    (ha : 0 < a) (hi : i <= a) (hj : j <= b)
    (hv : wordDrift P w ≠ (0, 0)) (hs : CopiesSeparated p q)
    (hc : Drift.SameClass (wordDrift P w)
      (wordPos w (p.phase i)) (wordPos w (q.phase j)))
    (hr : Drift.stableRank P w (p.phase i) < Drift.stableRank P w (q.phase j)) :
    (P : Int) * (eventLift q w j - eventLift p w i) <
      canonicalStart q w - canonicalStart p w := by
  let z := -Drift.lift (wordDrift P w) (p.pos w i)
  let u := -Drift.lift (wordDrift P w) (q.pos w j)
  have ht := (Drift.stableRank_lt_iff_stableTime_lt rfl hv
    (p.phase_lt i hi) (q.phase_lt j hj) hc).mp hr
  have hti : time (copy p z) i = Drift.stableTime (wordDrift P w) P w (p.phase i) := by
    rw [Drift.path_stableTime_eq p rfl hv i, time_copy]
    dsimp [z, time]
    rw [Int.neg_mul, Int.mul_comm (Drift.lift (wordDrift P w) (p.pos w i)) (P : Int)]
    omega
  have htj : time (copy q u) j = Drift.stableTime (wordDrift P w) P w (q.phase j) := by
    rw [Drift.path_stableTime_eq q rfl hv j, time_copy]
    dsimp [u, time]
    rw [Int.neg_mul, Int.mul_comm (Drift.lift (wordDrift P w) (q.pos w j)) (P : Int)]
    omega
  have horder : time (copy p z) a <= time (copy q u) 0 := by
    rcases hs z u with he | he
    · exact he
    · have hpi := time_eq (copy p z) hi
      have hqj := time_eq (copy q u) hj
      have hqb := time_eq (copy q u) (Nat.le_refl _)
      omega
  have hpa := time_eq (copy p z) (Nat.le_refl _)
  have hstart : time (copy p z) 0 < time (copy q u) 0 := by omega
  simp only [time_copy, z, u, Int.neg_mul] at hstart
  simp only [eventLift, canonicalStart, Int.mul_sub]
  rw [Int.mul_comm (Drift.lift (wordDrift P w) (p.pos w i)) (P : Int),
    Int.mul_comm (Drift.lift (wordDrift P w) (q.pos w j)) (P : Int)] at hstart
  omega

theorem eventLift_slice {P len : Nat} (p : ContinuousPhasePath P len)
    (w : Nat -> Bool) (a n : Nat) (h : a + n <= len) (r : Nat) :
    eventLift (slice p a n h) w r + eventLift p w a = eventLift p w (a + r) := by
  simp only [eventLift, slice, ContinuousPhasePath.pos, Nat.add_zero]
  omega

/-- Canonical-start offset of an actual subblock; the offset determines
the integer number of whole-drift copies used by a bridge contraction. -/
theorem canonicalStart_slice {P len : Nat} (p : ContinuousPhasePath P len)
    (w : Nat -> Bool) (a n : Nat) (h : a + n <= len) :
    canonicalStart (slice p a n h) w =
      canonicalStart p w + (a : Int) - (P : Int) * eventLift p w a := by
  have ht := time_eq p (show a <= len by omega)
  simp only [canonicalStart, eventLift, slice, time, ContinuousPhasePath.pos,
    Nat.add_zero, Int.mul_sub] at ht ⊢
  omega

/-- Round 24: the physical seam determines exactly the drift-copy increment.
For diagonal drift this is `(endX_U - startX_V) / m`, with no modular ambiguity. -/
theorem bridge_copy_increment {P a b : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P a) (q : ContinuousPhasePath P b) (u v : Int)
    (hv : wordDrift P w ≠ (0, 0))
    (h : time (copy p u) a = time (copy q v) 0) :
    v - u = Drift.lift (wordDrift P w) (p.pos w a) -
      Drift.lift (wordDrift P w) (q.pos w 0) := by
  have hp := pos_eq_of_time_eq (copy p u) (copy q v) (Nat.le_refl _) (by omega) h w
  rw [pos_copy, pos_copy] at hp
  have hl := congrArg (Drift.lift (wordDrift P w)) hp
  rw [Drift.lift_add_scale hv, Drift.lift_add_scale hv] at hl
  omega

theorem bridge_copy_increment_x {m P a b : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P a) (q : ContinuousPhasePath P b) (u v : Int)
    (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (h : time (copy p u) a = time (copy q v) 0) :
    v = u + ((p.pos w a).1 - (q.pos w 0).1) / (m : Int) := by
  have hp := pos_eq_of_time_eq (copy p u) (copy q v) (Nat.le_refl _) (by omega) h w
  rw [pos_copy, pos_copy, hd] at hp
  have hx := congrArg Prod.fst hp
  simp only [addPoint, scalePoint, diagDrift] at hx
  have he : (p.pos w a).1 - (q.pos w 0).1 = (v - u) * (m : Int) := by
    rw [Int.sub_mul]
    omega
  rw [he, Int.mul_ediv_cancel _ (show (m : Int) ≠ 0 by omega)]
  omega

/-- Round 24: the new weight is exactly `w + h_V - h_U`.
Here each parent is an actual subpath of its contracted block. -/
theorem contraction_weight {P lenA lenB : Nat}
    (p : ContinuousPhasePath P lenA) (q : ContinuousPhasePath P lenB)
    (w : Nat -> Bool) (a n b m i j : Nat)
    (ha : a + n <= lenA) (hb : b + m <= lenB) :
    eventLift q w (b + j) - eventLift p w (a + i) =
      (eventLift (slice q b m hb) w j - eventLift (slice p a n ha) w i) +
        eventLift q w b - eventLift p w a := by
  have hp := eventLift_slice p w a n ha i
  have hq := eventLift_slice q w b m hb j
  omega

/-- The cross-block test after contraction, using the corrected edge weight. -/
theorem contracted_rank_edge {P lenA lenB a n b m i j : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P lenA) (q : ContinuousPhasePath P lenB)
    (hpos : 0 < lenA) (ha : a + n <= lenA) (hb : b + m <= lenB)
    (hi : i <= n) (hj : j <= m) (hv : wordDrift P w ≠ (0, 0))
    (hs : CopiesSeparated p q)
    (hc : Drift.SameClass (wordDrift P w)
      (wordPos w (p.phase (a + i))) (wordPos w (q.phase (b + j))))
    (hr : Drift.stableRank P w (p.phase (a + i)) <
      Drift.stableRank P w (q.phase (b + j))) :
    (P : Int) * ((eventLift (slice q b m hb) w j - eventLift (slice p a n ha) w i) +
      eventLift q w b - eventLift p w a) < canonicalStart q w - canonicalStart p w := by
  rw [← contraction_weight p q w a n b m i j ha hb]
  exact blocks_rank_edge p q hpos (by omega) (by omega) hv hs hc hr

/-- Same-block criterion, also valid for boundary events of a contracted block. -/
theorem path_same_block_order {P len i j : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P len) (hlen : len <= P)
    (hi : i <= len) (hj : j <= len) (hv : wordDrift P w ≠ (0, 0))
    (ht : Drift.stableTime (wordDrift P w) P w (p.phase i) <
      Drift.stableTime (wordDrift P w) P w (p.phase j)) :
    eventLift p w j - eventLift p w i < 0 ∨
      (eventLift p w j - eventLift p w i = 0 ∧ i < j) := by
  rw [stableTime_event p hv hi, stableTime_event p hv hj] at ht
  by_cases h : eventLift p w j - eventLift p w i < 0
  · exact Or.inl h
  · have he : eventLift p w j - eventLift p w i = 0 := by
      by_cases he : eventLift p w j - eventLift p w i = 0
      · exact he
      · have hdif : 1 <= eventLift p w j - eventLift p w i := by omega
        have hm := Int.mul_le_mul_of_nonneg_left hdif (show (0 : Int) <= P by omega)
        rw [Int.mul_sub, Int.mul_one] at hm
        omega
    have he' : eventLift p w j = eventLift p w i := by omega
    rw [he'] at ht
    exact Or.inr ⟨he, by omega⟩

/-- Round 24: positive same-block weight is impossible; zero weight must
point strictly forward in the concatenated physical event order. -/
theorem contracted_same_block_order {P len a n b m i j : Nat} {w : Nat -> Bool}
    (p : ContinuousPhasePath P len) (hlen : len <= P)
    (ha : a + n <= len) (hb : b + m <= len) (hi : i <= n) (hj : j <= m)
    (hv : wordDrift P w ≠ (0, 0))
    (ht : Drift.stableTime (wordDrift P w) P w (p.phase (a + i)) <
      Drift.stableTime (wordDrift P w) P w (p.phase (b + j))) :
    let weight := (eventLift (slice p b m hb) w j - eventLift (slice p a n ha) w i) +
      eventLift p w b - eventLift p w a
    weight < 0 ∨ (weight = 0 ∧ a + i < b + j) := by
  dsimp only
  rw [← contraction_weight p p w a n b m i j ha hb]
  exact path_same_block_order p hlen (by omega) (by omega) hv ht

namespace Excursion

theorem copiesSeparated {P : Nat} {w : Nat -> Bool} {L : Int}
    (s t : Excursion P w L) (hd : layer (wordDrift P w) = 0)
    (hne : s.path.phase 0 ≠ t.path.phase 0) : CopiesSeparated s.path t.path := by
  intro z u
  have he : (s.translate z hd).start ≠ (t.translate u hd).start := by
    intro hh
    exact hne (biTime_injective (s.path.phase_lt 0 (by omega))
      (t.path.phase_lt 0 (by omega)) hh).2
  rcases Int.lt_trichotomy (s.translate z hd).start (t.translate u hd).start with h | h | h
  · exact Or.inl ((s.translate z hd).finish_le_start (t.translate u hd) h)
  · exact False.elim (he h)
  · exact Or.inr ((t.translate u hd).finish_le_start (s.translate z hd) h)

/-- Comparing any two interior events compares their entire distinct blocks. -/
theorem whole_segment_order {P i j : Nat} {w : Nat -> Bool} {L : Int}
    (s t : Excursion P w L) (hi : 0 < i) (hi' : i < s.len)
    (_hj : 0 < j) (hj' : j < t.len) (hne : s.start ≠ t.start)
    (ht : time s.path i < time t.path j) : s.finish <= t.start := by
  by_cases hs : s.start < t.start
  · exact s.finish_le_start t hs
  · have hrev := t.finish_le_start s (by omega)
    have hsi := time_eq s.path (show i <= s.len by omega)
    have htj := time_eq t.path (show j <= t.len by omega)
    have htf := t.finish_eq
    change time s.path i = s.start + (i : Int) at hsi
    change time t.path j = t.start + (j : Int) at htj
    omega

theorem len_le_period {P : Nat} {w : Nat -> Bool} {L : Int}
    (s : Excursion P w L) (hd : layer (wordDrift P w) = 0) : s.len <= P := by
  have hP : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le _) (s.path.phase_lt 0 (by omega))
  have hs : (s.translate 1 hd).start = s.start + (P : Int) := by
    change time (copy s.path 1) 0 = _
    rw [time_copy, Int.one_mul]
    rfl
  have hh := s.finish_le_start (s.translate 1 hd) (by rw [hs]; omega)
  rw [hs, s.finish_eq] at hh
  omega

/-- Round 21: a rank comparison between distinct segment orbits forces the
strict whole-segment inequality. Offsets do not occur in the conclusion. -/
theorem rank_edge {P i j : Nat} {w : Nat -> Bool} {L : Int}
    (s t : Excursion P w L) (hv : wordDrift P w ≠ (0, 0))
    (hd : layer (wordDrift P w) = 0)
    (hi : 0 < i) (hi' : i < s.len) (hj : 0 < j) (hj' : j < t.len)
    (hne : s.path.phase 0 ≠ t.path.phase 0)
    (hc : Drift.SameClass (wordDrift P w)
      (wordPos w (s.path.phase i)) (wordPos w (t.path.phase j)))
    (hr : Drift.stableRank P w (s.path.phase i) <
      Drift.stableRank P w (t.path.phase j)) :
    (P : Int) * (eventLift t.path w j - eventLift s.path w i) <
      canonicalStart t.path w - canonicalStart s.path w := by
  let a := s.translate (-Drift.lift (wordDrift P w) (s.path.pos w i)) hd
  let b := t.translate (-Drift.lift (wordDrift P w) (t.path.pos w j)) hd
  have hne' : a.start ≠ b.start := by
    intro he
    have hph := (biTime_injective (a.path.phase_lt 0 (by omega))
      (b.path.phase_lt 0 (by omega)) he).2
    exact hne hph
  have ht := (Drift.stableRank_lt_iff_stableTime_lt rfl hv
    (s.path.phase_lt i (by omega)) (t.path.phase_lt j (by omega)) hc).mp hr
  have hta : time a.path i = Drift.stableTime (wordDrift P w) P w (s.path.phase i) := by
    rw [Drift.path_stableTime_eq s.path rfl hv i]
    change time (copy s.path _) i = time s.path i - _
    rw [time_copy, Int.neg_mul, Int.mul_comm]
    omega
  have htb : time b.path j = Drift.stableTime (wordDrift P w) P w (t.path.phase j) := by
    rw [Drift.path_stableTime_eq t.path rfl hv j]
    change time (copy t.path _) j = time t.path j - _
    rw [time_copy, Int.neg_mul, Int.mul_comm]
    omega
  have ho := a.whole_segment_order b hi hi' hj hj' hne' (by rw [hta, htb]; exact ht)
  have haf := a.finish_eq
  have hal : 0 < a.len := by have := s.nonempty; exact Nat.lt_trans (by decide) this
  have hs : a.start < b.start := by omega
  change time (copy s.path _) 0 < time (copy t.path _) 0 at hs
  simp only [time_copy, Int.mul_comm, Int.mul_neg] at hs
  simp only [eventLift, canonicalStart, Int.mul_sub]
  omega

/-- Round 21: comparison inside one segment orbit uses lift first, then
event offset. A visit in the same physical copy is not a block edge. -/
theorem same_segment_order {P i j : Nat} {w : Nat -> Bool} {L : Int}
    (s : Excursion P w L) (hv : wordDrift P w ≠ (0, 0))
    (hd : layer (wordDrift P w) = 0)
    (hi : 0 < i) (hi' : i < s.len) (_hj : 0 < j) (hj' : j < s.len)
    (ht : Drift.stableTime (wordDrift P w) P w (s.path.phase i) <
      Drift.stableTime (wordDrift P w) P w (s.path.phase j)) :
    eventLift s.path w j < eventLift s.path w i ∨
      (eventLift s.path w i = eventLift s.path w j ∧ i < j) := by
  rw [stableTime_event s.path hv (by omega), stableTime_event s.path hv (by omega)] at ht
  have hlen := s.len_le_period hd
  by_cases h : eventLift s.path w j < eventLift s.path w i
  · exact Or.inl h
  · have he : eventLift s.path w i = eventLift s.path w j := by
      by_cases he : eventLift s.path w i = eventLift s.path w j
      · exact he
      · have hdif : 1 <= eventLift s.path w j - eventLift s.path w i := by omega
        have hm := Int.mul_le_mul_of_nonneg_left hdif (show (0 : Int) <= P by omega)
        rw [Int.mul_sub, Int.mul_one] at hm
        omega
    refine Or.inr ⟨he, ?_⟩
    rw [he] at ht
    omega

end Excursion

/-- Sum of edge weights along a finite, not necessarily simple, walk. -/
def weightSum (weight : Nat -> Int) : Nat -> Int
  | 0 => 0
  | n + 1 => weightSum weight n + weight n

theorem strict_walk_sum {n : Nat} (hn : 0 < n) (P : Nat)
    (X weight : Nat -> Int)
    (hedge : ∀ k, k < n -> (P : Int) * weight k < X (k + 1) - X k) :
    (P : Int) * weightSum weight n < X n - X 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [weightSum, Int.mul_add]
    have hl := hedge n (by omega)
    by_cases hz : n = 0
    · subst n
      simpa only [weightSum, Int.mul_zero, Int.zero_add] using hl
    · have hh := ih (by omega) (fun k hk => hedge k (by omega))
      omega

/-- Round 21: every nonempty directed cycle of whole-segment comparisons
has strictly negative total integer weight, independently of the period. -/
theorem cycle_weight_negative {P n : Nat} (hP : 0 < P) (hn : 0 < n)
    (X weight : Nat -> Int) (hclose : X n = X 0)
    (hedge : ∀ k, k < n -> (P : Int) * weight k < X (k + 1) - X k) :
    weightSum weight n < 0 := by
  have h := strict_walk_sum hn P X weight hedge
  rw [hclose, Int.sub_self] at h
  by_cases hw : weightSum weight n < 0
  · exact hw
  · have hh := Int.mul_nonneg (show (0 : Int) <= P by omega)
      (show 0 <= weightSum weight n by omega)
    omega

/-- Round 21 directly on physical excursions: every closed chain of
cross-orbit rank comparisons has negative total weight. -/
theorem physical_cycle_weight_negative {P n : Nat} {w : Nat -> Bool} {L : Int}
    (f : Nat -> Excursion P w L) (a b : Nat -> Nat) (hn : 0 < n)
    (hv : wordDrift P w ≠ (0, 0)) (hd : layer (wordDrift P w) = 0)
    (hclose : f n = f 0)
    (hinside : ∀ k, k < n ->
      0 < a k ∧ a k < (f k).len ∧ 0 < b k ∧ b k < (f (k + 1)).len)
    (hne : ∀ k, k < n -> (f k).path.phase 0 ≠ (f (k + 1)).path.phase 0)
    (hclass : ∀ k, k < n -> Drift.SameClass (wordDrift P w)
      (wordPos w ((f k).path.phase (a k))) (wordPos w ((f (k + 1)).path.phase (b k))))
    (hrank : ∀ k, k < n -> Drift.stableRank P w ((f k).path.phase (a k)) <
      Drift.stableRank P w ((f (k + 1)).path.phase (b k))) :
    weightSum (fun k => eventLift (f (k + 1)).path w (b k) -
      eventLift (f k).path w (a k)) n < 0 := by
  have hP : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le _) ((f 0).path.phase_lt 0 (by omega))
  apply cycle_weight_negative hP hn (fun k => canonicalStart (f k).path w) _
    (by rw [hclose])
  intro k hk
  obtain ⟨ha, ha', hb, hb'⟩ := hinside k hk
  exact (f k).rank_edge (f (k + 1)) hv hd ha ha' hb hb' (hne k hk)
    (hclass k hk) (hrank k hk)

namespace Excursion

def dx {P : Nat} {w : Nat -> Bool} {L : Int} (s : Excursion P w L) : Int :=
  (s.path.pos w s.len).1 - (s.path.pos w 0).1

theorem zero_dx_return {P : Nat} {w : Nat -> Bool} {L : Int}
    (s : Excursion P w L) (h : s.dx = 0) : s.path.pos w s.len = s.path.pos w 0 := by
  have h0 := s.start_layer
  have h1 := s.end_layer
  simp only [dx, layer, weight] at h h0 h1
  apply Prod.ext <;> omega

theorem departure {P : Nat} {w : Nat -> Bool} {L : Int} (s : Excursion P w L) :
    LangtonsAnt.beta w (s.path.phase 0) = true := by
  have ha := s.above 1 (by decide) s.nonempty
  have hs := s.path.layer_step (w := w) (show 0 < s.len by have := s.nonempty; omega)
  simp only [Nat.zero_add] at hs
  rw [s.start_layer] at hs
  unfold LangtonsAnt.beta
  cases he : outDir w (s.path.phase 0) <;> rw [he] at hs <;>
    simp_all [layerDelta] <;> omega

theorem arrival {P : Nat} {w : Nat -> Bool} {L : Int} (s : Excursion P w L)
    (hdir : (wordTrace w P).2 = .north) :
    LangtonsAnt.alpha w (s.path.phase s.len) = true := by
  have hn : s.len - 1 + 1 = s.len := by have := s.nonempty; omega
  have ha := s.above (s.len - 1) (by have := s.nonempty; omega) (by omega)
  have hs := s.path.layer_step (w := w) (r := s.len - 1) (by have := s.nonempty; omega)
  rw [hn, s.end_layer] at hs
  have hh := s.path.heading_step hdir (r := s.len - 1) (by have := s.nonempty; omega)
  change inDir w (s.path.phase (s.len - 1 + 1)) = outDir w (s.path.phase (s.len - 1)) at hh
  rw [hn] at hh
  unfold LangtonsAnt.alpha
  rw [hh]
  cases he : outDir w (s.path.phase (s.len - 1)) <;> rw [he] at hs <;>
    simp_all [layerDelta] <;> omega

/-- Round 23: exactly one endpoint of a zero-displacement parent is a
bridge. The other endpoint goes to the lower side. -/
theorem zero_endpoint_xor {P : Nat} {w : Nat -> Bool} {L : Int}
    (s : Excursion P w L) (hc : ConsistentWord P w)
    (hv : wordDrift P w ≠ (0, 0)) (hd : layer (wordDrift P w) = 0)
    (hz : s.dx = 0) :
    (LangtonsAnt.alpha w (s.path.phase 0) = false ∧
      LangtonsAnt.beta w (s.path.phase s.len) = true) ∨
    (LangtonsAnt.alpha w (s.path.phase 0) = true ∧
      LangtonsAnt.beta w (s.path.phase s.len) = false) := by
  have hret := s.zero_dx_return hz
  have hr := Drift.path_firstReturn_rank s.path rfl hv
    (by have := s.nonempty; omega) hret (by
      intro r hr hr' he
      have ha := s.above r hr hr'
      rw [he, s.start_layer] at ha
      omega)
  have hdep := s.departure
  have harr := s.arrival hc.1
  have h0 := beta_eq_xor_of_layer_zero hc hd (s.path.phase_lt 0 (by omega))
  have h1 := beta_eq_xor_of_layer_zero hc hd (s.path.phase_lt s.len (by omega))
  have hl : layer (wordPos w (s.path.phase s.len)) =
      layer (wordPos w (s.path.phase 0)) := by
    exact TwoCellDiagonal.layer_eq_of_sameClass hd
      ((Drift.path_sameClass_pos s.path rfl s.len).trans
        (hret ▸ (Drift.path_sameClass_pos s.path rfl 0).symm))
  have he : depth P w (s.path.phase s.len) = depth P w (s.path.phase 0) := by
    simp only [depth, hl]
  rw [he, hr, harr] at h1
  rw [hdep] at h0
  have hodd : decide ((Drift.stableRank P w (s.path.phase 0) + 1) % 2 = 1) =
      !decide (Drift.stableRank P w (s.path.phase 0) % 2 = 1) := by
    have hm := Nat.mod_two_eq_zero_or_one (Drift.stableRank P w (s.path.phase 0))
    rcases hm with hm | hm <;> simp [hm, Nat.add_mod]
  rw [hodd] at h1
  cases ha : LangtonsAnt.alpha w (s.path.phase 0) <;>
    cases hb : LangtonsAnt.beta w (s.path.phase s.len) <;>
    cases hk : decide (Drift.stableRank P w (s.path.phase 0) % 2 = 1) <;>
    cases he : decide (depth P w (s.path.phase 0) % 2 = 1) <;>
    simp [ha, hb, hk, he] at h0 h1 ⊢

end Excursion

/-- Exact decomposition of a child into consecutive parent excursions.
The list is represented by its ordered boundary times, including both ends.
These fields specify geometry only, not bridge choices or displacement laws. -/
structure ParentChain {P : Nat} {w : Nat -> Bool} {L : Int}
    (child : Excursion P w (L - 1)) where
  count : Nat
  cutAt : Nat -> Nat
  first : cutAt 0 = 1
  last : cutAt count = child.len - 1
  bounds : ∀ k, k <= count -> cutAt k <= child.len
  strict : ∀ k, k < count -> cutAt k < cutAt (k + 1)
  boundary : ∀ k, k <= count -> layer (child.path.pos w (cutAt k)) = L
  interior : ∀ k, k < count -> ∀ r, cutAt k < r -> r < cutAt (k + 1) ->
    L < layer (child.path.pos w r)

private structure LayerPartition (f : Nat -> Int) (L : Int) (a b : Nat) where
  count : Nat
  cutAt : Nat -> Nat
  first : cutAt 0 = a
  last : cutAt count = b
  bounds : ∀ k, k <= count -> a <= cutAt k ∧ cutAt k <= b
  strict : ∀ k, k < count -> cutAt k < cutAt (k + 1)
  boundary : ∀ k, k <= count -> f (cutAt k) = L
  interior : ∀ k, k < count -> ∀ r, cutAt k < r -> r < cutAt (k + 1) -> L < f r

private theorem exists_layerPartition (f : Nat -> Int) (L : Int)
    {a b : Nat} (hab : a <= b) (ha : f a = L) (hb : f b = L)
    (hl : ∀ r, a <= r -> r <= b -> L <= f r) : Nonempty (LayerPartition f L a b) := by
  have main : ∀ n a b, b - a = n -> a <= b -> f a = L -> f b = L ->
      (∀ r, a <= r -> r <= b -> L <= f r) -> Nonempty (LayerPartition f L a b) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b hn hab ha hb hl
      by_cases he : a = b
      · subst b
        exact ⟨⟨0, fun _ => a, rfl, rfl, by intros; omega,
          by intros; omega, by intros; exact ha, by intros; omega⟩⟩
      · obtain ⟨c, ⟨hac, hcb, hc⟩, hmin⟩ := exists_least
          (p := fun r => a < r ∧ r <= b ∧ f r = L) (b + 1) b (by omega) ⟨by omega, by omega, hb⟩
        obtain ⟨q⟩ := ih (b - c) (by omega) c b rfl hcb hc hb
          (fun r hr hr' => hl r (by omega) hr')
        let cuts : Nat -> Nat := fun k => if k = 0 then a else q.cutAt (k - 1)
        refine ⟨⟨q.count + 1, cuts, by simp [cuts], ?_, ?_, ?_, ?_, ?_⟩⟩
        · simpa [cuts] using q.last
        · intro k hk
          cases k with
          | zero => simpa [cuts] using hab
          | succ k =>
            have hh := q.bounds k (by omega)
            simp only [cuts, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
              ite_false, Nat.add_sub_cancel]
            omega
        · intro k hk
          cases k with
          | zero => simpa [cuts, q.first] using hac
          | succ k => simpa [cuts] using q.strict k (by omega)
        · intro k hk
          cases k with
          | zero => simpa [cuts] using ha
          | succ k => simpa [cuts] using q.boundary k (by omega)
        · intro k hk r hr hr'
          cases k with
          | zero =>
            have har : a < r := by simpa [cuts] using hr
            have hrc : r < c := by simpa [cuts, q.first] using hr'
            have hge := hl r (by omega) (by omega)
            have hne : f r ≠ L := fun he => hmin r hrc ⟨har, by omega, he⟩
            omega
          | succ k =>
            exact q.interior k (by omega) r (by simpa [cuts] using hr)
              (by simpa [cuts] using hr')
  exact main (b - a) a b rfl hab ha hb hl

/-- Every physical child admits the exact parent decomposition; existence
is proved from its layer trace, not imposed as an additional hypothesis. -/
theorem exists_parentChain {P : Nat} {w : Nat -> Bool} {L : Int}
    (c : Excursion P w (L - 1)) : Nonempty (ParentChain c) := by
  have hn := c.nonempty
  have hfirst : layer (c.path.pos w 1) = L := by
    have hs := c.path.layer_step (w := w) (r := 0) (by omega)
    simp only [Nat.zero_add] at hs
    have ha := c.above 1 (by decide) hn
    rw [c.start_layer] at hs
    cases hd : outDir w (c.path.phase 0) <;> rw [hd] at hs <;>
      simp only [layerDelta] at hs <;> omega
  have hlast : layer (c.path.pos w (c.len - 1)) = L := by
    have hs := c.path.layer_step (w := w) (r := c.len - 1) (by omega)
    have ha := c.above (c.len - 1) (by omega) (by omega)
    rw [show c.len - 1 + 1 = c.len by omega, c.end_layer] at hs
    cases hd : outDir w (c.path.phase (c.len - 1)) <;> rw [hd] at hs <;>
      simp only [layerDelta] at hs <;> omega
  obtain ⟨q⟩ := exists_layerPartition (fun r => layer (c.path.pos w r)) L
    (a := 1) (b := c.len - 1) (by omega) hfirst hlast (by
      intro r hr hr'
      have := c.above r (by omega) (by omega)
      omega)
  exact ⟨⟨q.count, q.cutAt, q.first, q.last,
    fun k hk => by have := q.bounds k hk; omega, q.strict, q.boundary, q.interior⟩⟩

namespace ParentChain

theorem cutAt_mono {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) {i j : Nat}
    (hij : i <= j) (hj : j <= q.count) : q.cutAt i <= q.cutAt j := by
  induction j with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i <= j
    · have hh := ih he (by omega)
      have hs := q.strict j (by omega)
      omega
    · have he : i = j + 1 := by omega
      rw [he]
      exact Nat.le_refl _

theorem cutAt_strict {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) {i j : Nat}
    (hij : i < j) (hj : j <= q.count) : q.cutAt i < q.cutAt j := by
  have hh := q.cutAt_mono (i := i + 1) (j := j) (by omega) hj
  have hs := q.strict i (by omega)
  omega

/-- Every visit to the newly added layer occurs at exactly one chain
boundary. There are no omitted visits or duplicated parent junctions. -/
theorem boundary_complete {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) {r : Nat}
    (hr : 1 <= r) (hr' : r <= c.len - 1) (hl : layer (c.path.pos w r) = L) :
    ∃ k, k <= q.count ∧ q.cutAt k = r ∧
      ∀ j, j <= q.count -> q.cutAt j = r -> j = k := by
  obtain ⟨k, ⟨hk, hkr⟩, hmin⟩ := exists_least
    (p := fun k => k <= q.count ∧ r <= q.cutAt k) (q.count + 1) q.count
    (by omega) ⟨Nat.le_refl _, by rw [q.last]; exact hr'⟩
  have he : q.cutAt k = r := by
    by_cases hk0 : k = 0
    · rw [hk0, q.first] at hkr ⊢
      omega
    · have hprev : q.cutAt (k - 1) < r := by
        have hh := hmin (k - 1) (by omega)
        omega
      by_cases hh : r < q.cutAt k
      · have hn : k - 1 + 1 = k := by omega
        have ha := q.interior (k - 1) (by omega) r hprev (by rw [hn]; exact hh)
        rw [hl] at ha
        omega
      · omega
  refine ⟨k, hk, he, ?_⟩
  intro j hj hjr
  rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
  · have hh := q.cutAt_strict hjk hk
    omega
  · exact hjk
  · have hh := q.cutAt_strict hjk hj
    omega

private theorem boundary_match {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q t : ParentChain c) {i : Nat} (hi : i <= q.count) :
    i <= t.count ∧ q.cutAt i = t.cutAt i := by
  induction i with
  | zero => exact ⟨Nat.zero_le _, q.first.trans t.first.symm⟩
  | succ i ih =>
    obtain ⟨hit, he⟩ := ih (by omega)
    have hlow := q.cutAt_mono (i := 0) (j := i + 1) (Nat.zero_le _) hi
    have hupp := q.cutAt_mono (i := i + 1) (j := q.count) hi (Nat.le_refl _)
    rw [q.first] at hlow
    rw [q.last] at hupp
    obtain ⟨j, hj, hjq, _⟩ := t.boundary_complete hlow hupp (q.boundary (i + 1) hi)
    have hij : i < j := by
      by_cases hh : j <= i
      · have hm := t.cutAt_mono hh hit
        have hs := q.strict i (by omega)
        omega
      · omega
    have hje : j = i + 1 := by
      by_cases hh : i + 1 < j
      · have hs0 := t.strict i (by omega)
        have hs1 := t.cutAt_strict hh hj
        have ha := q.interior i (by omega) (t.cutAt (i + 1)) (by omega) (by omega)
        rw [t.boundary (i + 1) (by omega)] at ha
        omega
      · omega
    exact ⟨by omega, by simpa only [hje] using hjq.symm⟩

/-- The canonical decomposition is unique on all relevant boundary times;
the unrestricted tail of the indexing function is intentionally ignored. -/
theorem unique {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q t : ParentChain c) :
    q.count = t.count ∧ ∀ i, i <= q.count -> q.cutAt i = t.cutAt i := by
  have hq := boundary_match q t (Nat.le_refl q.count)
  have ht := boundary_match t q (Nat.le_refl t.count)
  exact ⟨by omega, fun i hi => (boundary_match q t hi).2⟩

/-- Every parent excursion occurring inside this child is exactly one
consecutive pair of its boundary visits. -/
theorem parent_complete {P a b : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c)
    (ha : 1 <= a) (hab : a < b) (hb : b <= c.len - 1)
    (hal : layer (c.path.pos w a) = L) (hbl : layer (c.path.pos w b) = L)
    (habove : ∀ r, a < r -> r < b -> L < layer (c.path.pos w r)) :
    ∃ k, k < q.count ∧ q.cutAt k = a ∧ q.cutAt (k + 1) = b := by
  obtain ⟨i, hi, hia, _⟩ := q.boundary_complete ha (by omega) hal
  obtain ⟨j, hj, hjb, _⟩ := q.boundary_complete (by omega) hb hbl
  have hij : i < j := by
    by_cases hh : j <= i
    · have hm := q.cutAt_mono hh hi
      omega
    · omega
  have he : j = i + 1 := by
    by_cases hh : i + 1 < j
    · have hl := q.strict i (by omega)
      have hr := q.cutAt_strict hh hj
      have hf := habove (q.cutAt (i + 1)) (by omega) (by omega)
      rw [q.boundary (i + 1) (by omega)] at hf
      omega
    · omega
  exact ⟨i, by omega, hia, by rw [← he]; exact hjb⟩

theorem gap {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) {k : Nat} (hk : k < q.count) :
    1 < q.cutAt (k + 1) - q.cutAt k := by
  have hs := q.strict k hk
  have hb := q.bounds (k + 1) (by omega)
  have hstep := c.path.layer_step (w := w) (r := q.cutAt k) (by omega)
  have hleft := q.boundary k (by omega)
  have hright := q.boundary (k + 1) (by omega)
  by_cases hn : q.cutAt (k + 1) = q.cutAt k + 1
  · rw [← hn, hleft, hright] at hstep
    cases hd : outDir w (c.path.phase (q.cutAt k)) <;> rw [hd] at hstep <;>
      simp only [layerDelta] at hstep <;> omega
  · omega

def parent {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) (k : Nat) (hk : k < q.count) :
    Excursion P w L where
  len := q.cutAt (k + 1) - q.cutAt k
  path := slice c.path (q.cutAt k) (q.cutAt (k + 1) - q.cutAt k)
    (by have := q.strict k hk; have := q.bounds (k + 1) (by omega); omega)
  nonempty := q.gap hk
  start_layer := by
    change layer (c.path.pos w (q.cutAt k + 0)) = L
    simpa only [Nat.add_zero] using q.boundary k (by omega)
  end_layer := by
    change layer (c.path.pos w (q.cutAt k + (q.cutAt (k + 1) - q.cutAt k))) = L
    rw [Nat.add_sub_of_le (Nat.le_of_lt (q.strict k hk))]
    exact q.boundary (k + 1) (by omega)
  above r hr hr' := by
    change L < layer (c.path.pos w (q.cutAt k + r))
    exact q.interior k hk _ (by omega) (by have := q.strict k hk; omega)

theorem parent_phase_start {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) (k : Nat) (hk : k < q.count) :
    (q.parent k hk).path.phase 0 = c.path.phase (q.cutAt k) := by
  simp only [parent, slice, Nat.add_zero]

theorem parent_phase_end {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) (k : Nat) (hk : k < q.count) :
    (q.parent k hk).path.phase (q.parent k hk).len = c.path.phase (q.cutAt (k + 1)) := by
  simp only [parent, slice, Nat.add_sub_of_le (Nat.le_of_lt (q.strict k hk))]

theorem parent_adjacent_time {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) {k : Nat} (hk : k + 1 < q.count) :
    time (q.parent k (by omega)).path (q.parent k (by omega)).len =
      time (q.parent (k + 1) hk).path 0 := by
  simp only [parent, slice, time, Nat.add_zero,
    Nat.add_sub_of_le (Nat.le_of_lt (q.strict k (by omega)))]

theorem parent_block_bound {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c)
    (hd : layer (wordDrift P w) = 0) {i j : Nat} (_hij : i <= j) (hj : j <= q.count) :
    q.cutAt j - q.cutAt i <= P := by
  have hlen := c.len_le_period hd
  have hb := q.bounds j hj
  omega

theorem start_alpha_false {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c)
    (hdir : (wordTrace w P).2 = .north) :
    LangtonsAnt.alpha w (c.path.phase (q.cutAt 0)) = false := by
  rw [q.first]
  have hh := c.path.heading_step hdir (r := 0) (by have := c.nonempty; omega)
  change inDir w (c.path.phase 1) = outDir w (c.path.phase 0) at hh
  have hs := c.path.layer_step (w := w) (r := 0) (by have := c.nonempty; omega)
  have ha := c.above 1 (by decide) c.nonempty
  rw [c.start_layer] at hs
  unfold LangtonsAnt.alpha
  rw [hh]
  cases hd : outDir w (c.path.phase 0) <;> rw [hd] at hs <;>
    simp_all [layerDelta] <;> omega

theorem end_beta_false {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) :
    LangtonsAnt.beta w (c.path.phase (q.cutAt q.count)) = false := by
  rw [q.last]
  have hn : c.len - 1 + 1 = c.len := by have := c.nonempty; omega
  have hs := c.path.layer_step (w := w) (r := c.len - 1) (by have := c.nonempty; omega)
  rw [hn, c.end_layer] at hs
  have ha := c.above (c.len - 1) (by have := c.nonempty; omega) (by omega)
  unfold LangtonsAnt.beta
  cases hd : outDir w (c.path.phase (c.len - 1)) <;> rw [hd] at hs <;>
    simp_all [layerDelta] <;> omega

/-- Round 23: a zero parent is an endpoint of its child chain and has
exactly one neighbor. In particular it is neither isolated nor internal. -/
theorem zero_parent_endpoint {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c)
    (hc : ConsistentWord P w) (hv : wordDrift P w ≠ (0, 0))
    (hd : layer (wordDrift P w) = 0) {k : Nat} (hk : k < q.count)
    (hz : (q.parent k hk).dx = 0) :
    (k = 0 ∧ k + 1 < q.count) ∨ (0 < k ∧ k + 1 = q.count) := by
  have hx := (q.parent k hk).zero_endpoint_xor hc hv hd hz
  rw [q.parent_phase_start, q.parent_phase_end] at hx
  rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hk0 : k = 0 := by
      by_cases he : k = 0
      · exact he
      · have hn : k - 1 + 1 = k := by omega
        have hprev := (q.parent (k - 1) (by omega)).arrival hc.1
        rw [q.parent_phase_end, hn, ha] at hprev
        contradiction
    have hn : k + 1 < q.count := by
      by_cases he : k + 1 = q.count
      · rw [he, q.end_beta_false] at hb
        contradiction
      · omega
    exact Or.inl ⟨hk0, hn⟩
  · have hk0 : 0 < k := by
      by_cases he : k = 0
      · rw [he, q.start_alpha_false hc.1] at ha
        contradiction
      · omega
    have hn : k + 1 = q.count := by
      by_cases he : k + 1 < q.count
      · have hnext := (q.parent (k + 1) he).departure
        rw [q.parent_phase_start, hb] at hnext
        contradiction
      · omega
    exact Or.inr ⟨hk0, hn⟩

theorem all_zero_count_two {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c)
    (hc : ConsistentWord P w) (hv : wordDrift P w ≠ (0, 0))
    (hd : layer (wordDrift P w) = 0) (hne : 0 < q.count)
    (hz : ∀ k (hk : k < q.count), (q.parent k hk).dx = 0) : q.count = 2 := by
  have h0 := q.zero_parent_endpoint hc hv hd hne (hz 0 hne)
  have h1lt : 1 < q.count := by omega
  have h1 := q.zero_parent_endpoint hc hv hd h1lt (hz 1 h1lt)
  omega

theorem interior_parent_nonzero {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c)
    (hc : ConsistentWord P w) (hv : wordDrift P w ≠ (0, 0))
    (hd : layer (wordDrift P w) = 0) {k : Nat}
    (hk : 0 < k) (hk' : k + 1 < q.count) :
    (q.parent k (by omega)).dx ≠ 0 := by
  intro hz
  have hh := q.zero_parent_endpoint hc hv hd (by omega) hz
  omega

def parentDx {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) (k : Nat) : Int :=
  (c.path.pos w (q.cutAt (k + 1))).1 - (c.path.pos w (q.cutAt k)).1

theorem parentDx_eq {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) {k : Nat} (hk : k < q.count) :
    q.parentDx k = (q.parent k hk).dx := by
  simp only [parentDx, Excursion.dx, parent, slice, ContinuousPhasePath.pos,
    Nat.add_zero, Nat.add_sub_of_le (Nat.le_of_lt (q.strict k hk))]

theorem sum_parentDx {P : Nat} {w : Nat -> Bool} {L : Int}
    {c : Excursion P w (L - 1)} (q : ParentChain c) :
    weightSum q.parentDx q.count =
      (c.path.pos w (c.len - 1)).1 - (c.path.pos w 1).1 := by
  have hh : ∀ n, weightSum q.parentDx n =
      (c.path.pos w (q.cutAt n)).1 - (c.path.pos w (q.cutAt 0)).1 := by
    intro n
    induction n with
    | zero => simp [weightSum]
    | succ n ih => simp only [weightSum, ih, parentDx]; omega
  simpa only [q.first, q.last] using hh q.count

/-- Round 23: exact physical x displacement, including both exterior
crossing steps. The sign is the parity of the newly added layer. -/
theorem child_displacement {P n : Nat} {w : Nat -> Bool}
    {c : Excursion P w (topLayer P w - (n : Int) - 1)} (q : ParentChain c)
    (hc : ConsistentWord P w) (hd : layer (wordDrift P w) = 0) :
    c.dx = (if n % 2 = 0 then 1 else -1) + weightSum q.parentDx q.count := by
  have hlift (r : Nat) : layer (wordPos w (c.path.phase r)) = layer (c.path.pos w r) :=
    TwoCellDiagonal.layer_eq_of_sameClass hd (Drift.path_sameClass_pos c.path rfl r)
  have hdep : LangtonsAnt.alpha w (c.path.phase 1) = false := by
    simpa only [q.first] using q.start_alpha_false hc.1
  have harr : LangtonsAnt.beta w (c.path.phase (c.len - 1)) = false := by
    simpa only [q.last] using q.end_beta_false
  have hf := q.boundary 0 (Nat.zero_le _)
  rw [q.first] at hf
  have he := q.boundary q.count (Nat.le_refl _)
  rw [q.last] at he
  have hdepth0 : depth P w (c.path.phase 1) = (n : Int) := by
    simp only [depth, hlift, hf]
    omega
  have hdepth1 : depth P w (c.path.phase (c.len - 1)) = (n : Int) := by
    simp only [depth, hlift, he]
    omega
  have hin := inDir_eq_of_depth_alpha_of_layer_zero hc hd (c.path.phase 1)
  have hout := outDir_eq_of_depth_beta_of_layer_zero hc hd (c.path.phase (c.len - 1))
  rw [hdep, hdepth0] at hin
  rw [harr, hdepth1] at hout
  have hheading := c.path.heading_step hc.1 (r := 0) (by have := c.nonempty; omega)
  change inDir w (c.path.phase 1) = outDir w (c.path.phase 0) at hheading
  have hfirst := c.path.pos_step (w := w) (r := 0) (by have := c.nonempty; omega)
  have hlast := c.path.pos_step (w := w) (r := c.len - 1) (by have := c.nonempty; omega)
  change c.path.pos w 1 = move (c.path.pos w 0) (outDir w (c.path.phase 0)) at hfirst
  change c.path.pos w (c.len - 1 + 1) = move (c.path.pos w (c.len - 1))
    (outDir w (c.path.phase (c.len - 1))) at hlast
  rw [show c.len - 1 + 1 = c.len by have := c.nonempty; omega] at hlast
  rw [← hheading, hin] at hfirst
  rw [hout] at hlast
  rw [q.sum_parentDx]
  unfold Excursion.dx
  by_cases hp : n % 2 = 0
  · have hp' : (n : Int) % 2 = 0 := by omega
    simp only [hp, hp', ite_true, Bool.false_eq_true, ite_false] at hfirst hlast ⊢
    have hx0 := congrArg Prod.fst hfirst
    have hx1 := congrArg Prod.fst hlast
    simp only [move] at hx0 hx1
    omega
  · have hp' : ¬(n : Int) % 2 = 0 := by omega
    simp only [hp, hp', ite_false, Bool.false_eq_true] at hfirst hlast ⊢
    have hx0 := congrArg Prod.fst hfirst
    have hx1 := congrArg Prod.fst hlast
    simp only [move] at hx0 hx1
    omega

end ParentChain

namespace Excursion

/-- A zero parent cannot have bridges at both ends, even when the other
parents are supplied only as genuine phase-matched physical excursions. -/
theorem zero_no_two_bridges {P : Nat} {w : Nat -> Bool} {L : Int}
    (p s t : Excursion P w L) (hc : ConsistentWord P w)
    (hv : wordDrift P w ≠ (0, 0)) (hd : layer (wordDrift P w) = 0)
    (hz : s.dx = 0) (hp : p.path.phase p.len = s.path.phase 0)
    (ht : s.path.phase s.len = t.path.phase 0) : False := by
  have ha := p.arrival hc.1
  rw [hp] at ha
  have hb := t.departure
  rw [← ht] at hb
  rcases s.zero_endpoint_xor hc hv hd hz with h | h
  · rw [ha] at h
    simp at h
  · rw [hb] at h
    simp at h

/-- Round 24: a closed parent-bridge cycle containing a zero parent is
impossible. Cycles without a zero parent are deliberately not excluded. -/
theorem zero_no_bridge_cycle {P n : Nat} {w : Nat -> Bool} {L : Int}
    (f : Nat -> Excursion P w L) (hn : 0 < n) (hc : ConsistentWord P w)
    (hv : wordDrift P w ≠ (0, 0)) (hd : layer (wordDrift P w) = 0)
    (hz : (f 0).dx = 0) (hclose : f n = f 0)
    (hedge : ∀ k, k < n -> (f k).path.phase (f k).len = (f (k + 1)).path.phase 0) : False := by
  have hp := hedge (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega, hclose] at hp
  exact zero_no_two_bridges (f (n - 1)) (f 0) (f 1) hc hv hd hz hp (hedge 0 hn)

/-- The segment interface produces the existing physical `UpperReturn`
interface, including genuine ordered ports rather than extra lookup assumptions. -/
theorem upperReturn_of_zero {m P n : Nat} {w : Nat -> Bool}
    (s : Excursion P w (topLayer P w - (n : Int)))
    (hc : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (hz : s.dx = 0) :
    ∃ j i, DiagonalReturnOrder.UpperReturn m P w n (s.path.pos w 0).1 j i := by
  have hv := diagDrift_ne_zero hm
  have hp : s.path.pos w 0 =
      laneCell (topLayer P w - (n : Int)) (s.path.pos w 0).1 := by
    have hl := s.start_layer
    simp only [layer, weight] at hl
    apply Prod.ext <;> simp only [laneCell] <;> omega
  have hret := s.zero_dx_return hz
  have hmem0 : s.path.phase 0 ∈ Drift.classPhases (diagDrift m) P w
      (laneCell (topLayer P w - (n : Int)) (s.path.pos w 0).1) := by
    apply Drift.mem_classPhases.mpr
    exact ⟨s.path.phase_lt 0 (by omega), hp ▸ Drift.path_sameClass_pos s.path hd 0⟩
  have hmem1 : s.path.phase s.len ∈ Drift.classPhases (diagDrift m) P w
      (laneCell (topLayer P w - (n : Int)) (s.path.pos w 0).1) := by
    apply Drift.mem_classPhases.mpr
    refine ⟨s.path.phase_lt s.len (by omega), ?_⟩
    have hh := Drift.path_sameClass_pos s.path hd s.len
    rw [hret, hp] at hh
    exact hh
  have hbeta := classBetaWord_at_phase hd hv hmem0
  have halpha := classAlphaWord_at_phase hd hv hmem1
  rw [s.departure] at hbeta
  rw [s.arrival hc.1] at halpha
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (UnitDiagonal.mem_trueIdx.mpr hbeta)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (UnitDiagonal.mem_trueIdx.mpr halpha)
  refine ⟨j, i, s.len, s.path, by have := s.nonempty; omega, hp, hret, ?_, hj, hi⟩
  intro r hr hr'
  rw [s.start_layer]
  exact s.above r hr hr'

end Excursion

/-- Round 24, with the forbidden end of each branch stated explicitly.
This strengthens the two-branch port lemma to the exact bridge/exclusion pair. -/
theorem zeroReturn_forced_bridge {a : List Bool} {e : Bool} {j i : Nat}
    (h : DiagonalReturnOrder.ZeroReturn a e j i) :
    ∃ k, (UnitDiagonal.trueIdx (UnitDiagonal.beta a e))[j]? = some k ∧
      (UnitDiagonal.trueIdx a)[i]? = some (k + 1) ∧
      ((a[k]? = some false ∧
        (UnitDiagonal.trueIdx (UnitDiagonal.beta a e))[j + 1]? = some (k + 1)) ∨
       (0 < i ∧ (UnitDiagonal.trueIdx a)[i - 1]? = some k ∧
        (UnitDiagonal.beta a e)[k + 1]? = some false)) := by
  obtain ⟨k, hq, hp⟩ := h
  refine ⟨k, hq, hp, ?_⟩
  by_cases he : (k + 1) % 2 = (if e then 1 else 0)
  · exact Or.inl ⟨UnitDiagonal.bridge_parity_alpha_false e hq he,
      UnitDiagonal.bridge_parity e hp hq he⟩
  · obtain ⟨hi, hprev⟩ := UnitDiagonal.bridge_opposite e hp hq he
    exact Or.inr ⟨hi, hprev, UnitDiagonal.bridge_opposite_beta_false e hp he⟩

theorem upperReturn_forced_bridge {m P n j i : Nat} {w : Nat -> Bool} {r : Int}
    (hc : ConsistentWord P w) (hm : 0 < m) (hd : wordDrift P w = diagDrift m)
    (h : DiagonalReturnOrder.UpperReturn m P w n r j i) :
    let a := laneAlpha m P w (topLayer P w - (n : Int)) r
    let e := decide (n % 2 = 1)
    ∃ k, (UnitDiagonal.trueIdx (UnitDiagonal.beta a e))[j]? = some k ∧
      (UnitDiagonal.trueIdx a)[i]? = some (k + 1) ∧
      ((a[k]? = some false ∧
        (UnitDiagonal.trueIdx (UnitDiagonal.beta a e))[j + 1]? = some (k + 1)) ∨
       (0 < i ∧ (UnitDiagonal.trueIdx a)[i - 1]? = some k ∧
        (UnitDiagonal.beta a e)[k + 1]? = some false)) :=
  zeroReturn_forced_bridge (DiagonalReturnOrder.upperReturn_zeroReturn hc hm hd h)

/-- Round 32: east entries on one physical vertical line have equal
height parity, including arbitrary positive or negative period copies. -/
theorem east_entries_same_y_parity {P i j : Nat} {w : Nat -> Bool} {a b : Int}
    (hc : ConsistentWord P w)
    (hi : inDir w i = .east) (hj : inDir w j = .east)
    (hx : (biPeriodicPos P w a i).1 = (biPeriodicPos P w b j).1) :
    (biPeriodicPos P w a i).2 % 2 = (biPeriodicPos P w b j).2 % 2 := by
  have hi' := (inDir_horizontal_iff w i).mp (by simp [hi, Direction.horizontal])
  have hj' := (inDir_horizontal_iff w j).mp (by simp [hj, Direction.horizontal])
  have hd := hc.drift_sum_even
  have ha := Int.mul_emod a ((wordDrift P w).1 + (wordDrift P w).2) 2
  have hb := Int.mul_emod b ((wordDrift P w).1 + (wordDrift P w).2) 2
  rw [hd] at ha hb
  simp only [Int.mul_zero, Int.zero_emod, Int.mul_add] at ha hb
  simp only [layer, weight] at hi' hj'
  simp only [biPeriodicPos, addPoint, scalePoint] at hx ⊢
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The standard word's child from phase 0 to phase 86, above layer 0. -/
def stdChild : Excursion 104 TwoCellDiagonal.stdHighwaySE 0 where
  len := 86
  path := ContinuousPhasePath.ofStart (by decide) 0 86
  nonempty := by decide
  start_layer := by decide +kernel
  end_layer := by decide +kernel
  above r hr hr' := by
    have h : ∀ r : Fin 86, 0 < r.val ->
        0 < layer ((ContinuousPhasePath.ofStart (by decide : 0 < 104) 0 86).pos
          TwoCellDiagonal.stdHighwaySE r.val) := by decide +kernel
    exact h ⟨r, hr'⟩ hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The actual parent chain is `1 -> 9 -> 85`; both parents return to `(1,0)`. -/
def stdChain : ParentChain (L := 1) stdChild where
  count := 2
  cutAt k := if k = 0 then 1 else if k = 1 then 9 else 85
  first := rfl
  last := rfl
  bounds k hk := by
    have h : ∀ k : Fin 3, (if k.val = 0 then 1 else if k.val = 1 then 9 else 85) <=
        stdChild.len := by decide +kernel
    exact h ⟨k, by omega⟩
  strict k hk := by
    have h : ∀ k : Fin 2,
        (if k.val = 0 then 1 else if k.val = 1 then 9 else 85) <
        (if k.val + 1 = 0 then 1 else if k.val + 1 = 1 then 9 else 85) := by decide
    exact h ⟨k, hk⟩
  boundary k hk := by
    have h : ∀ k : Fin 3,
        layer (stdChild.path.pos TwoCellDiagonal.stdHighwaySE
          (if k.val = 0 then 1 else if k.val = 1 then 9 else 85)) = 1 := by decide +kernel
    exact h ⟨k, by omega⟩
  interior k hk r hr hr' := by
    have h : ∀ k : Fin 2, ∀ r : Fin 86,
        (if k.val = 0 then 1 else if k.val = 1 then 9 else 85) < r.val ->
        r.val < (if k.val + 1 = 0 then 1 else if k.val + 1 = 1 then 9 else 85) ->
        1 < layer (stdChild.path.pos TwoCellDiagonal.stdHighwaySE r.val) := by decide +kernel
    have hr86 : r < 86 := by split at hr' <;> (try split at hr') <;> omega
    exact h ⟨k, hk⟩ ⟨r, hr86⟩ hr hr'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem stdChain_parents_zero :
    ∀ k (hk : k < stdChain.count), (stdChain.parent k hk).dx = 0 := by
  have h : ∀ k : Fin 2, stdChain.parentDx k.val = 0 := by decide +kernel
  intro k hk
  rw [← stdChain.parentDx_eq hk]
  exact h ⟨k, hk⟩

/-- Non-vacuity of rounds 23--24 on the genuine period-104 word: a child
of displacement `+1` contains exactly two zero-displacement parents. -/
theorem stdHighwaySE_nonvacuity :
    ConsistentWord 104 TwoCellDiagonal.stdHighwaySE ∧
    wordDrift 104 TwoCellDiagonal.stdHighwaySE = (2, -2) ∧
    stdChain.count = 2 ∧ stdChild.dx = 1 ∧
    (∀ k (hk : k < stdChain.count), (stdChain.parent k hk).dx = 0) := by
  refine ⟨TwoCellDiagonal.stdHighwaySE_consistent, TwoCellDiagonal.stdHighwaySE_drift,
    ?_, ?_, stdChain_parents_zero⟩
  · exact stdChain.all_zero_count_two TwoCellDiagonal.stdHighwaySE_consistent
      (by rw [TwoCellDiagonal.stdHighwaySE_drift]; decide)
      (by rw [TwoCellDiagonal.stdHighwaySE_drift]; decide) (by decide) stdChain_parents_zero
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- An actual cross-segment rank edge in the standard word, comparing
the interior visits at phases 2 and 10. -/
theorem stdHighwaySE_rank_edge :
    let s := stdChain.parent 0 (by decide)
    let t := stdChain.parent 1 (by decide)
    (104 : Int) * (eventLift t.path TwoCellDiagonal.stdHighwaySE 1 -
      eventLift s.path TwoCellDiagonal.stdHighwaySE 1) <
      canonicalStart t.path TwoCellDiagonal.stdHighwaySE -
        canonicalStart s.path TwoCellDiagonal.stdHighwaySE := by
  dsimp only
  apply Excursion.rank_edge
    (s := stdChain.parent 0 (by decide)) (t := stdChain.parent 1 (by decide))
  · rw [TwoCellDiagonal.stdHighwaySE_drift]; decide
  · rw [TwoCellDiagonal.stdHighwaySE_drift]; decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact ⟨0, by decide +kernel⟩
  · decide +kernel

end LangtonsAnt.DiagonalSegments
