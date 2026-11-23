import UnitDiagonal
import TwoCellDiagonalExtremal

/-!
# Roots of consistent periodic turn words

The period hypothesis refers to the infinite read sequence, not just to a finite
prefix. `ConsistentWord P w` alone does not constrain `w` beyond index `P - 1`.
For a finite word one can apply these results to `repeatWord P w`.

A shorter read period restores the heading whenever it divides a period with
restored heading and nonzero drift. The reason is that its rotation must fix
the full drift. Consistency then descends using the existing finite-support
realization and periodic-tail consistency theorems.
-/

namespace LangtonsAnt.RootWord

/-- A period of the entire one-sided read sequence (equivalently its periodic
two-sided extension when the period is positive). -/
def ReadPeriod (q : Nat) (w : Nat -> Bool) : Prop :=
  forall n, w (n + q) = w n

theorem ReadPeriod.mul {q : Nat} {w : Nat -> Bool} (h : ReadPeriod q w)
    (k : Nat) : ReadPeriod (q * k) w := by
  induction k with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    rw [Nat.mul_succ, <- Nat.add_assoc, h, ih]

theorem ReadPeriod.of_dvd {q P : Nat} {w : Nat -> Bool} (h : ReadPeriod q w)
    (hd : q ∣ P) : ReadPeriod P w := by
  obtain ⟨k, rfl⟩ := hd
  exact h.mul k

theorem ReadPeriod.mod_eq {q : Nat} {w : Nat -> Bool} (h : ReadPeriod q w)
    (n : Nat) : w (n % q) = w n := by
  have he := h.mul (n / q) (n % q)
  rw [Nat.add_comm, Nat.div_add_mod] at he
  exact he.symm

theorem ReadPeriod.repeat_eq {q : Nat} {w : Nat -> Bool} (h : ReadPeriod q w) :
    repeatWord q w = w := funext h.mod_eq

theorem repeatWord_period (P : Nat) (w : Nat -> Bool) :
    ReadPeriod P (repeatWord P w) := by
  intro n
  simp only [repeatWord, Nat.add_mod_right]

/-- The usual least positive period of an infinite read sequence. -/
def LeastReadPeriod (q : Nat) (w : Nat -> Bool) : Prop :=
  0 < q ∧ ReadPeriod q w ∧ forall r, 0 < r -> ReadPeriod r w -> q ≤ r

theorem ReadPeriod.mod {P q : Nat} {w : Nat -> Bool}
    (hP : ReadPeriod P w) (hq : ReadPeriod q w) : ReadPeriod (P % q) w := by
  intro n
  have he := hq.mul (P / q) (n + P % q)
  have hn : n + P % q + q * (P / q) = n + P := by
    have := Nat.div_add_mod P q
    omega
  rw [hn, hP n] at he
  exact he.symm

theorem LeastReadPeriod.dvd {P q : Nat} {w : Nat -> Bool}
    (hq : LeastReadPeriod q w) (hP : ReadPeriod P w) : q ∣ P := by
  apply Nat.dvd_of_mod_eq_zero
  have hlt := Nat.mod_lt P hq.1
  by_cases hz : P % q = 0
  · exact hz
  · have := hq.2.2 (P % q) (by omega) (hP.mod hq.2.1)
    omega

theorem exists_least_read_period {P : Nat} {w : Nat -> Bool}
    (hP : 0 < P) (hr : ReadPeriod P w) : exists q, LeastReadPeriod q w := by
  classical
  have hex : forall n, 0 < n -> ReadPeriod n w -> exists q, LeastReadPeriod q w := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn hp
      by_cases hs : exists r, r < n ∧ 0 < r ∧ ReadPeriod r w
      · obtain ⟨r, hrn, hrpos, hrper⟩ := hs
        exact ih r hrn hrpos hrper
      · refine ⟨n, hn, hp, ?_⟩
        intro r hrpos hrper
        by_cases hnr : n ≤ r
        · exact hnr
        · exact False.elim (hs ⟨r, by omega, hrpos, hrper⟩)
  exact hex P hP hr

/-- A read period acts on the whole trace by its accumulated rigid motion;
no heading-restoration assumption is used here. -/
theorem trace_period_rigid {q : Nat} {w : Nat -> Bool} (h : ReadPeriod q w)
    (n : Nat) :
    wordTrace w (n + q) =
      (addPoint (wordDrift q w) (rotatePoint (wordTrace w q).2 (wordPos w n)),
        rotateDir (wordTrace w q).2 (wordTrace w n).2) := by
  induction n with
  | zero => simp [wordPos, wordTrace, wordDrift]
  | succ n ih =>
    rw [show n + 1 + q = (n + q) + 1 by omega]
    simp only [wordTrace, ih, h n, wordPos, rotatePoint_move, rotateDir_turn,
      move_addPoint]

/-- A quarter turn fixing a nonzero lattice vector is the identity. -/
theorem rotation_eq_north_of_fixed {r : Direction} {v : Point}
    (hv : v ≠ (0, 0)) (he : rotatePoint r v = v) : r = .north := by
  cases r with
  | north => rfl
  | east =>
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    simp only [rotatePoint] at hx hy
    exact False.elim (hv (Prod.ext (by omega) (by omega)))
  | south =>
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    simp only [rotatePoint] at hx hy
    exact False.elim (hv (Prod.ext (by omega) (by omega)))
  | west =>
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    simp only [rotatePoint] at hx hy
    exact False.elim (hv (Prod.ext (by omega) (by omega)))

/-- In fact divisibility is unnecessary here: any two read periods commute. -/
theorem period_heading {P q : Nat} {w : Nat -> Bool}
    (hP : ReadPeriod P w) (hq : ReadPeriod q w)
    (hd : (wordTrace w P).2 = .north) (hv : wordDrift P w ≠ (0, 0)) :
    (wordTrace w q).2 = .north := by
  have ha := congrArg Prod.fst (trace_period_rigid hq P)
  have hb := congrArg Prod.fst (trace_period_rigid hP q)
  rw [Nat.add_comm P q] at ha
  have he := ha.symm.trans hb
  simp only [hd, rotatePoint] at he
  change addPoint (wordDrift q w) (rotatePoint (wordTrace w q).2 (wordDrift P w)) =
    addPoint (wordDrift P w) (wordDrift q w) at he
  apply rotation_eq_north_of_fixed hv
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  apply Prod.ext <;> simp only [addPoint] at hx hy <;> omega

theorem trace_period {q : Nat} {w : Nat -> Bool} (hq : ReadPeriod q w)
    (hd : (wordTrace w q).2 = .north) (n : Nat) :
    wordTrace w (n + q) =
      (addPoint (wordDrift q w) (wordPos w n), (wordTrace w n).2) := by
  simpa only [hd, rotatePoint, rotateDir] using trace_period_rigid hq n

theorem drift_mul {q : Nat} {w : Nat -> Bool} (hq : ReadPeriod q w)
    (hd : (wordTrace w q).2 = .north) (k : Nat) :
    wordDrift (q * k) w = scalePoint (wordDrift q w) (k : Int) := by
  have he := repeatWord_pos_blocks hd k 0
  simpa only [hq.repeat_eq, Nat.add_zero, wordPos, wordTrace, addPoint, scalePoint,
    Int.zero_add, wordDrift] using he

/-- Transfer consistency along the same finite-support realization. This avoids
introducing a separate bijection between the two infinite-past phase lists. -/
theorem consistent_of_heading {P q : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (hq : 0 < q)
    (hp : ReadPeriod P w) (hr : ReadPeriod q w)
    (hd : (wordTrace w q).2 = .north) : ConsistentWord q w := by
  have hh : HighwayFrom (wordRealization P w) 0 q (wordDrift q w) := by
    intro n _
    rw [h.realization_run hP, h.realization_run hP]
    have ht := trace_period hr hd (P * (2 * P) + n)
    have hx := congrArg Prod.fst ht
    have hy := congrArg Prod.snd ht
    constructor
    · simpa only [prescribedState, hp.repeat_eq, wordPos, Nat.add_assoc, addPoint,
        Int.add_comm] using hx
    · simpa only [prescribedState, hp.repeat_eq, Nat.add_assoc] using hy
  have hc := periodic_tail_consistent_at_start (wordRealization_finite P w) hq hh
  apply hc.congr
  intro i _
  simp only [Nat.zero_add, h.realization_reads hP, hp.mod_eq]

/-- Root extraction for any positive read period dividing `P`; minimality of
the root period and diagonality of the drift are not needed. -/
theorem root_word {P q : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (hq : 0 < q)
    (hdiv : q ∣ P) (hr : ReadPeriod q w) :
    ConsistentWord q w ∧
      wordDrift P w = scalePoint (wordDrift q w) ((P / q : Nat) : Int) := by
  have hp := hr.of_dvd hdiv
  have hd := period_heading hp hr h.1 h.2.1
  refine ⟨consistent_of_heading h hP hq hp hr hd, ?_⟩
  have he := drift_mul hr hd (P / q)
  simpa only [Nat.mul_div_cancel' hdiv] using he

/-- Diagonal root extraction, including the exact integral quotient. The
positivity assumption chooses the southeast orientation of the diagonal. -/
theorem root_word_diagonal {P q m : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (hq : 0 < q)
    (hdiv : q ∣ P) (hr : ReadPeriod q w) (hm : 0 < m)
    (hv : wordDrift P w = ((m : Int), -(m : Int))) :
    ConsistentWord q w ∧ (P / q) ∣ m ∧
      wordDrift q w = (((m / (P / q) : Nat) : Int), -((m / (P / q) : Nat) : Int)) ∧
      0 < m / (P / q) := by
  obtain ⟨hc, hs⟩ := root_word h hP hq hdiv hr
  have hell : 0 < P / q := Nat.div_pos (Nat.le_of_dvd hP hdiv) hq
  have hne : ((P / q : Nat) : Int) ≠ 0 := by omega
  rw [hv] at hs
  have hx := congrArg Prod.fst hs
  have hy := congrArg Prod.snd hs
  simp only [scalePoint] at hx hy
  have hdm : (P / q) ∣ m := Int.ofNat_dvd.mp ⟨(wordDrift q w).1, hx⟩
  have hxx : (wordDrift q w).1 = ((m / (P / q) : Nat) : Int) := by
    rw [Int.natCast_ediv, hx, Int.mul_ediv_cancel_left _ hne]
  have hyy : (wordDrift q w).2 = -(wordDrift q w).1 := by
    apply (Int.mul_eq_mul_left_iff hne).mp
    rw [Int.mul_neg, <- hx]
    exact hy.symm
  exact ⟨hc, hdm, Prod.ext hxx (by rw [hyy, hxx]),
    Nat.div_pos (Nat.le_of_dvd hm hdm) hell⟩

/-- Elementary natural-number primality, without Mathlib. -/
def Prime (m : Nat) : Prop :=
  2 ≤ m ∧ forall d : Nat, d ∣ m -> d = 1 ∨ d = m

/-- A prime full diagonal drift excludes every proper positive divisor period
of the read sequence. -/
theorem prime_drift_minimal {P q m : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hm : Prime m)
    (hv : wordDrift P w = ((m : Int), -(m : Int)))
    (hq : 0 < q) (hqP : q < P) (hdiv : q ∣ P) (hr : ReadPeriod q w) : False := by
  obtain ⟨hc, hdm, hd, _⟩ := root_word_diagonal h (by omega) hq hdiv hr (by
    have := hm.1
    omega) hv
  rcases hm.2 (P / q) hdm with he | he
  · have hp := Nat.mul_div_cancel' hdiv
    rw [he, Nat.mul_one] at hp
    omega
  · have hmn : 0 < m := by have := hm.1; omega
    rw [he, Nat.div_self hmn] at hd
    apply _root_.UnitDiagonal.consistentWord_not_unitDiagonal' hc
    rw [hd]
    simp [_root_.UnitDiagonal.UnitDiagonalDrift]

/-- The finite word's canonical periodic extension has a consistent least
root, and the number of copies divides the positive diagonal magnitude. -/
theorem least_root_diagonal {P m : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (hm : 0 < m)
    (hv : wordDrift P w = ((m : Int), -(m : Int))) :
    exists q, LeastReadPeriod q (repeatWord P w) ∧ q ∣ P ∧
      ConsistentWord q w ∧ (P / q) ∣ m ∧
      wordDrift q w = (((m / (P / q) : Nat) : Int), -((m / (P / q) : Nat) : Int)) ∧
      0 < m / (P / q) := by
  obtain ⟨q, hq⟩ := exists_least_read_period hP (repeatWord_period P w)
  have hdiv := hq.dvd (repeatWord_period P w)
  have hqP := hq.2.2 P hP (repeatWord_period P w)
  have hc : ConsistentWord P (repeatWord P w) :=
    h.congr (fun i hi => (repeatWord_prefix w hi).symm)
  obtain ⟨hr, hdm, hd, hpos⟩ := root_word_diagonal hc hP hq.1 hdiv hq.2.1 hm
    (by rw [repeatWord_drift]; exact hv)
  refine ⟨q, hq, hdiv, hr.congr (fun i hi => repeatWord_prefix w (by omega)), hdm, ?_, hpos⟩
  have he := congrArg Prod.fst (repeatWord_trace w hqP)
  change wordDrift q (repeatWord P w) = wordDrift q w at he
  exact he.symm.trans hd

/-- With prime full diagonal drift, `P` is the least positive read period of
the canonical periodic extension, not merely minimal among divisor periods. -/
theorem prime_drift_least {P m : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (hm : Prime m)
    (hv : wordDrift P w = ((m : Int), -(m : Int))) :
    LeastReadPeriod P (repeatWord P w) := by
  obtain ⟨q, hq⟩ := exists_least_read_period hP (repeatWord_period P w)
  have hdiv := hq.dvd (repeatWord_period P w)
  have hqP := hq.2.2 P hP (repeatWord_period P w)
  have he : q = P := by
    by_cases he : q = P
    · exact he
    · have hc : ConsistentWord P (repeatWord P w) :=
        h.congr (fun i hi => (repeatWord_prefix w hi).symm)
      exact False.elim (prime_drift_minimal hc hm
        (by rw [repeatWord_drift]; exact hv) hq.1 (by omega) hdiv hq.2.1)
  rw [he] at hq
  exact hq

/-- An odd positive diagonal drift remains odd after root extraction. Its
positive root magnitude is at least three, by unit-diagonal exclusion. -/
theorem odd_drift_root {P q m : Nat} {w : Nat -> Bool}
    (h : ConsistentWord P w) (hP : 0 < P) (hq : 0 < q)
    (hdiv : q ∣ P) (hr : ReadPeriod q w) (hm : m % 2 = 1)
    (hv : wordDrift P w = ((m : Int), -(m : Int))) :
    ConsistentWord q w ∧
      wordDrift q w = (((m / (P / q) : Nat) : Int), -((m / (P / q) : Nat) : Int)) ∧
      (m / (P / q)) % 2 = 1 ∧ 3 ≤ m / (P / q) := by
  obtain ⟨hc, hdm, hd, hpos⟩ := root_word_diagonal h hP hq hdiv hr (by omega) hv
  have hmul := Nat.mul_div_cancel' hdm
  have hodd : (m / (P / q)) % 2 = 1 := by
    have he := congrArg (fun n => n % 2) hmul
    rw [Nat.mul_mod, hm] at he
    by_cases hz : (m / (P / q)) % 2 = 0
    · simp only [hz, Nat.mul_zero, Nat.zero_mod] at he
      omega
    · omega
  have hnot : m / (P / q) ≠ 1 := by
    intro he
    apply _root_.UnitDiagonal.consistentWord_not_unitDiagonal' hc
    rw [hd, he]
    simp [_root_.UnitDiagonal.UnitDiagonalDrift]
  exact ⟨hc, hd, hodd, by omega⟩

theorem heading_mul {q : Nat} {w : Nat -> Bool} (hr : ReadPeriod q w)
    (hd : (wordTrace w q).2 = .north) (k : Nat) :
    (wordTrace w (q * k)).2 = .north := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ]
    exact (congrArg Prod.snd (trace_period hr hd (q * k))).trans ih

/-- Positive powers of a periodic consistent word remain consistent. -/
theorem power_word {q : Nat} {w : Nat -> Bool} (h : ConsistentWord q w)
    (hq : 0 < q) (hr : ReadPeriod q w) {k : Nat} (hk : 0 < k) :
    ConsistentWord (q * k) w ∧
      wordDrift (q * k) w = scalePoint (wordDrift q w) (k : Int) :=
  ⟨consistent_of_heading h hq (Nat.mul_pos hq hk) hr (hr.mul k)
      (heading_mul hr h.1 k), drift_mul hr h.1 k⟩

theorem stdHighwaySE_period : ReadPeriod 104 TwoCellDiagonal.stdHighwaySE := by
  intro n
  simp only [TwoCellDiagonal.stdHighwaySE, repeatWord, <- Nat.add_assoc,
    Nat.add_mod_right]

/-- The known 104-step standard word gives a consistent 208-step power with
drift `(4,-4)` and a consistent root with drift `(2,-2)`. No enumeration of
208-step consistency certificates is needed. -/
theorem stdHighwaySE_power_nonvacuity :
    ConsistentWord 208 TwoCellDiagonal.stdHighwaySE ∧
      wordDrift 208 TwoCellDiagonal.stdHighwaySE = (4, -4) ∧
      ConsistentWord 104 TwoCellDiagonal.stdHighwaySE ∧
      wordDrift 104 TwoCellDiagonal.stdHighwaySE = (2, -2) ∧
      ReadPeriod 104 TwoCellDiagonal.stdHighwaySE := by
  obtain ⟨hc, hd⟩ := power_word TwoCellDiagonal.stdHighwaySE_consistent
    (by decide) stdHighwaySE_period (k := 2) (by decide)
  refine ⟨hc, ?_, TwoCellDiagonal.stdHighwaySE_consistent,
    TwoCellDiagonal.stdHighwaySE_drift, stdHighwaySE_period⟩
  rw [TwoCellDiagonal.stdHighwaySE_drift] at hd
  exact hd

/-- Phase shifting the standard word preserves its least positive read period.
The only finite calculation is the already certified standard-word result. -/
theorem stdHighwaySE_minimal {q : Nat} (hq : 0 < q) (hsmall : q < 104) :
    ¬ ReadPeriod q TwoCellDiagonal.stdHighwaySE := by
  intro hr
  obtain ⟨j, hj⟩ := highwayWord_no_short_period ⟨q, hsmall⟩ hq
  have he := hr (j.val + 97)
  have hleft : TwoCellDiagonal.stdHighwaySE (j.val + 97 + q) =
      certifiedColor (j.val + q) := by
    simp only [TwoCellDiagonal.stdHighwaySE, repeatWord, certifiedColor, Nat.mod_mod]
    congr 2
    omega
  have hright : TwoCellDiagonal.stdHighwaySE (j.val + 97) = certifiedColor j.val := by
    simp only [TwoCellDiagonal.stdHighwaySE, repeatWord, certifiedColor, Nat.mod_mod]
    congr 2
    omega
  exact hj (hleft.symm.trans (he.trans hright))

end LangtonsAnt.RootWord
