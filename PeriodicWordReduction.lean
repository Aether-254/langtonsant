import PeriodicWord
import Ballistic

namespace LangtonsAnt

/-- A purely finite-word classification obligation, not an assumed theorem.
The comparison window is a common multiple of both word lengths. -/
def ConsistentWordsAreStandard : Prop :=
  forall P (w : Nat -> Bool), 0 < P -> ConsistentWord P w ->
    exists a, a < P ∧ forall n, n < 104 * P -> w ((a + n) % P) = certifiedColor n

theorem finite_word_standard_extends {P a : Nat} {w : Nat -> Bool} (hP : 0 < P)
    (h : forall n, n < 104 * P -> w ((a + n) % P) = certifiedColor n) (n : Nat) :
    w ((a + n) % P) = certifiedColor n := by
  have hm := Nat.mod_lt n (Nat.mul_pos (by decide : 0 < 104) hP)
  have hpmod : (n % (104 * P)) % P = n % P :=
    Nat.mod_mod_of_dvd n (Nat.dvd_mul_left P 104)
  have h104 : (n % (104 * P)) % 104 = n % 104 :=
    Nat.mod_mod_of_dvd n (Nat.dvd_mul_right 104 P)
  have hh := h (n % (104 * P)) hm
  have hmod : (a + n % (104 * P)) % P = (a + n) % P := by
    rw [Nat.add_mod, Nat.add_mod a n P, hpmod]
  simpa only [hmod, certifiedColor, h104] using hh

theorem consistentWordsAreStandard_implies_periodicIsStandard
    (hc : ConsistentWordsAreStandard) : PeriodicIsStandard := by
  intro s hs hper
  obtain ⟨T, P, v, hP, hh⟩ := hper
  obtain ⟨a, _, ha⟩ := hc P (fun i => readColor s (T + i)) hP
    (periodic_tail_consistent_at_start hs hP hh)
  have ht : HighwayFrom (run s T) 0 P v := by
    intro n _
    simpa only [← run_add, Nat.add_assoc] using hh (T + n) (by omega)
  have hreads (n : Nat) : readColor s (T + n) = readColor s (T + n % P) := by
    have he := (ht.word_blocks (n / P) (n % P)).2
    simpa only [Nat.div_add_mod, readColor, ← run_add] using he
  let t := run s (T + a)
  let u := normalize t.dir t.pos t
  have hup : u.pos = (0, 0) := by
    have hz : addPoint (negPoint t.pos) t.pos = (0, 0) := by
      apply Prod.ext <;> simp only [addPoint, negPoint] <;> omega
    change rotatePoint (inverseRotation t.dir) (addPoint (negPoint t.pos) t.pos) = _
    rw [hz, rotatePoint_zero]
  have hud : u.dir = .north := by
    change rotateDir (inverseRotation t.dir) t.dir = .north
    simpa only [rotateDir_north] using rotateDir_inverse t.dir .north
  have hur (n : Nat) : readColor u n = standardColor n := by
    rw [show readColor u n = readColor t n from normalize_readColor t.dir t.pos t n]
    change readColor (run s (T + a)) n = _
    have he : readColor (run s (T + a)) n = readColor s (T + (a + n)) := by
      simp only [readColor, ← run_add, Nat.add_assoc]
    rw [he, hreads (a + n), finite_word_standard_extends (a := a)
      (w := fun i => readColor s (T + i)) hP ha n,
      standardColor_eq_certifiedColor]
  have hu : EventuallyStandard u :=
    ⟨0, (-2, -2), by simp [DiagonalDrift], standard_reads_highway hup hud hur⟩
  have hp := hu.pose t.dir t.pos
  have he : pose t.dir t.pos u = t := pose_normalize t.dir t.pos t
  rw [he] at hp
  exact EventuallyStandard.of_run hp

theorem highwayConjecture_of_ballistic_and_consistentWordsAreStandard
    (hb : forall s : State, FiniteSupport s.board -> Ballistic s)
    (hc : ConsistentWordsAreStandard) : HighwayConjecture :=
  highwayConjecture_iff_ballistic_and_periodicIsStandard.mpr
    ⟨hb, consistentWordsAreStandard_implies_periodicIsStandard hc⟩

end LangtonsAnt
