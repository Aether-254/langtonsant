import DirectionTableTranslation
import RootWord

/-!
# A diagonal table translation shortens the read period

If a lane translation `(a,-a)` with `0 < a < m` preserves every rank-indexed direction table of a
consistent word with full drift `(m,-m)`, then the induced phase map is the cyclic shift
`i ↦ (F 0 + i) mod P` (`F_eq_shift`), `F 0` is a read period of the periodic extension
(`tables_read_period`), and `0 < F 0 < P`, so `P` is not the least read period
(`diagonal_tables_not_least`).  The existence of such a translation is NOT proved here.

Pure kernel proofs; no `native_decide`.  Source: research/persist-B-diagonal-m3-2026-11-22.md,
session 4 (GPT-6 Astra), checked there in a scratch file and integrated unchanged.
-/

namespace LangtonsAnt.DiagonalTablePeriod

open DirectionTableTranslation

theorem cyclic_commuting_eq {P : Nat} {f : Nat -> Nat}
    (hP : 0 < P) (hzero : f 0 < P)
    (hcomm : forall i, i < P -> f ((i + 1) % P) = (f i + 1) % P)
    (n : Nat) : f (n % P) = (f 0 + n) % P := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt hzero]
  | succ n ih =>
    have ha : (n % P + 1) % P = (n + 1) % P := by simp [Nat.add_mod]
    have hb : ((f 0 + n) % P + 1) % P = (f 0 + (n + 1)) % P := by
      rw [<- Nat.add_assoc]
      simp only [Nat.add_mod, Nat.mod_mod]
    calc
      f ((n + 1) % P) = f ((n % P + 1) % P) := congrArg f ha.symm
      _ = (f (n % P) + 1) % P := hcomm _ (Nat.mod_lt _ hP)
      _ = ((f 0 + n) % P + 1) % P := by rw [ih]
      _ = (f 0 + (n + 1)) % P := hb

theorem F_eq_shift {v b : Point} {P i : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : Not (v = (0, 0)))
    (h : PreservesTables v P w b) (hi : i < P) :
    F hd hv h i = (F hd hv h 0 + i) % P := by
  have hP := hw.pos_period
  have hzero := (Drift.mem_classPhases.mp (F_spec hd hv h hP).1).1
  have hcomm : forall j, j < P ->
      F hd hv h ((j + 1) % P) = (F hd hv h j + 1) % P := by
    intro j hj
    exact F_succ hw hd hv h hj
  have he := cyclic_commuting_eq hP hzero hcomm i
  rwa [Nat.mod_eq_of_lt hi] at he

theorem tables_read_period {v b : Point} {P : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : Not (v = (0, 0)))
    (h : PreservesTables v P w b) :
    RootWord.ReadPeriod (F hd hv h 0) (repeatWord P w) := by
  intro n
  have hr : n % P < P := Nat.mod_lt _ hw.pos_period
  have hc := F_color hw hd hv h hr
  rw [F_eq_shift hw hd hv h hr] at hc
  have he : (F hd hv h 0 + n % P) % P = (n + F hd hv h 0) % P := by
    simp [Nat.add_mod, Nat.add_comm]
  rw [he] at hc
  exact hc

theorem diagonal_shift_nonzero {P : Nat} {m a : Int} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (m, -m))
    (hv : Not ((m, -m) = ((0 : Int), (0 : Int))))
    (h : PreservesTables (m, -m) P w (a, -a))
    (hm : 0 < m) (ha : 0 < a) (ham : a < m) : 0 < F hd hv h 0 := by
  by_cases hz : 0 < F hd hv h 0
  · exact hz
  have hzero : F hd hv h 0 = 0 := by omega
  have hs := (Drift.mem_classPhases.mp (F_spec hd hv h hw.pos_period).1).2
  rw [hzero] at hs
  obtain ⟨z, he⟩ := hs
  have hx := congrArg Prod.fst he
  simp only [wordPos, wordTrace, addPoint, scalePoint, Int.zero_add] at hx
  by_cases hz : z <= 0
  · have hnonpos : z * m <= 0 := Int.mul_nonpos_of_nonpos_of_nonneg hz (by omega)
    omega
  · have hge : m <= z * m := by
      have hh := Int.mul_le_mul_of_nonneg_right (show (1 : Int) <= z by omega)
        (show 0 <= m by omega)
      simpa only [Int.one_mul] using hh
    omega

theorem diagonal_tables_not_least {P : Nat} {m a : Int} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (m, -m))
    (hv : Not ((m, -m) = ((0 : Int), (0 : Int))))
    (h : PreservesTables (m, -m) P w (a, -a))
    (hm : 0 < m) (ha : 0 < a) (ham : a < m) :
    Not (RootWord.LeastReadPeriod P (repeatWord P w)) := by
  intro hleast
  have hpos := diagonal_shift_nonzero hw hd hv h hm ha ham
  have hsmall := (Drift.mem_classPhases.mp (F_spec hd hv h hw.pos_period).1).1
  have hperiod := tables_read_period hw hd hv h
  have hh := hleast.2.2 _ hpos hperiod
  omega

end LangtonsAnt.DiagonalTablePeriod
