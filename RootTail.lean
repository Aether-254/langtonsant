import RootWord

/-!
# Eventual tails bound the root drift

Period arithmetic for least roots.  An eventual read period `q` of a sequence with least period
`P` gives `P ≤ q` (`eventual_period_bounds_least`).  If a coordinate `x` advances by `m` per
`P` steps and eventually by `u ≥ 0` per `q` steps, then `m ≤ u` (`tail_drift_bounds_root`); with
`u = 2` and `m ≥ 2` this forces `m = 2` and `P = q` (`tail_two_exact_root`).  The lemmas are
stated for an arbitrary integer coordinate `x`; applying them to a real trajectory needs its
horizontal position, which advances by the full drift each period.

Pure kernel proofs; no `native_decide`.  Source: research/persist-B-diagonal-m3-2026-11-22.md,
session 4 (GPT-6 Astra), checked there in a scratch file and integrated unchanged.
-/

namespace LangtonsAnt.RootTail

open RootWord

theorem period_of_eventual_period {P q N : Nat} {w : Nat -> Bool}
    (hP : 0 < P) (hp : ReadPeriod P w)
    (ht : forall n, N <= n -> w (n + q) = w n) : ReadPeriod q w := by
  intro n
  have hlarge : N <= n + P * N := by
    have hh : N <= P * N := by
      calc
        N = 1 * N := by omega
        _ <= P * N := Nat.mul_le_mul_right N hP
    omega
  have he := ht (n + P * N) hlarge
  have hl := hp.mul N (n + q)
  have hr := hp.mul N n
  rw [show n + P * N + q = n + q + P * N by omega] at he
  exact hl.symm.trans (he.trans hr)

theorem eventual_period_bounds_least {P q N : Nat} {w : Nat -> Bool}
    (hp : LeastReadPeriod P w) (hq : 0 < q)
    (ht : forall n, N <= n -> w (n + q) = w n) : P <= q := by
  exact hp.2.2 q hq (period_of_eventual_period hp.1 hp.2.1 ht)

theorem shift_mul {P : Nat} {f : Nat -> Int} {v : Int}
    (h : forall n, f (n + P) = f n + v) (k n : Nat) :
    f (n + P * k) = f n + (k : Int) * v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, <- Nat.add_assoc, h, ih]
    simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    omega

theorem shift_of_eventual {P q N : Nat} {f : Nat -> Int} {v u : Int}
    (hP : 0 < P) (hp : forall n, f (n + P) = f n + v)
    (ht : forall n, N <= n -> f (n + q) = f n + u) :
    forall n, f (n + q) = f n + u := by
  intro n
  have hh : N <= P * N := by
    calc
      N = 1 * N := by omega
      _ <= P * N := Nat.mul_le_mul_right N hP
  have he := ht (n + P * N) (by omega)
  have hl := shift_mul hp N (n + q)
  have hr := shift_mul hp N n
  rw [show n + P * N + q = n + q + P * N by omega] at he
  omega

theorem shifts_commensurate {P q : Nat} {f : Nat -> Int} {v u : Int}
    (hp : forall n, f (n + P) = f n + v)
    (hq : forall n, f (n + q) = f n + u) :
    (q : Int) * v = (P : Int) * u := by
  have a := shift_mul hp q 0
  have b := shift_mul hq P 0
  simp only [Nat.zero_add] at a b
  rw [Nat.mul_comm q P] at b
  omega

theorem standard_tail_bounds_root {P N : Nat} {m : Int}
    {w : Nat -> Bool} {x : Nat -> Int}
    (hleast : LeastReadPeriod P w)
    (hread : forall n, N <= n -> w (n + 104) = w n)
    (hpose : forall n, x (n + P) = x n + m)
    (htail : forall n, N <= n -> x (n + 104) = x n + 2) : m <= 2 := by
  have hsmall := eventual_period_bounds_least hleast (by decide : 0 < 104) hread
  have hstep := shift_of_eventual hleast.1 hpose htail
  have hratio := shifts_commensurate hpose hstep
  omega

theorem tail_drift_bounds_root {P q N : Nat} {m u : Int}
    {w : Nat -> Bool} {x : Nat -> Int}
    (hleast : LeastReadPeriod P w) (hq : 0 < q) (hu : 0 <= u)
    (hread : forall n, N <= n -> w (n + q) = w n)
    (hpose : forall n, x (n + P) = x n + m)
    (htail : forall n, N <= n -> x (n + q) = x n + u) : m <= u := by
  have hsmall := eventual_period_bounds_least hleast hq hread
  have hstep := shift_of_eventual hleast.1 hpose htail
  have hratio := shifts_commensurate hpose hstep
  have hb : (P : Int) * u <= (q : Int) * u :=
    Int.mul_le_mul_of_nonneg_right (by omega) hu
  rw [<- hratio] at hb
  exact Int.le_of_mul_le_mul_left hb (by omega)

theorem tail_two_exact_root {P q N : Nat} {m : Int}
    {w : Nat -> Bool} {x : Nat -> Int}
    (hleast : LeastReadPeriod P w) (hq : 0 < q) (hm : 2 <= m)
    (hread : forall n, N <= n -> w (n + q) = w n)
    (hpose : forall n, x (n + P) = x n + m)
    (htail : forall n, N <= n -> x (n + q) = x n + 2) : m = 2 /\ P = q := by
  have hb := tail_drift_bounds_root hleast hq (by decide : (0 : Int) <= 2)
    hread hpose htail
  have hstep := shift_of_eventual hleast.1 hpose htail
  have hratio := shifts_commensurate hpose hstep
  have he : m = 2 := by omega
  rw [he] at hratio
  exact And.intro he (by omega)

end LangtonsAnt.RootTail
