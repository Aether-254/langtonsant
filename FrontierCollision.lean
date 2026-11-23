import RootTail

/-!
# Frontier-state collisions

Region-restricted state agreement propagates along the ant run while the ant stays in the region
(`RegionEq.run`); a collision of frontier states after a positive time shifts the whole future
(`region_shift_future`), and a collision at a time shorter than the least read period contradicts
minimality (`frontier_collision_not_least`).  Also: diagonal tail alignment of heights, trimming
never-read cells does not change the trace (`trimFuture_trace`), and the first read of a cell
forces its initial colour (`initial_color_forced`).

The existence of a collision for real words (the key step of target B) is NOT proved here.
Pure kernel proofs; no `native_decide`.  Source: research/persist-B-diagonal-m3-2026-11-22.md,
session 6 (GPT-6 Astra), checked there in a scratch file and integrated unchanged.
-/


namespace LangtonsAnt.FrontierCollision

structure RegionEq (R : Point -> Prop) (s t : State) : Prop where
  pos : s.pos = t.pos
  dir : s.dir = t.dir
  board : forall p, R p -> s.board p = t.board p

theorem RegionEq.step {R : Point -> Prop} {s t : State}
    (h : RegionEq R s t) (hp : R t.pos) : RegionEq R (step s) (step t) := by
  have hc : s.board s.pos = t.board t.pos := by
    rw [h.pos]
    exact h.board _ hp
  refine { pos := ?_, dir := ?_, board := ?_ }
  · change move s.pos (turn (s.board s.pos) s.dir) = _
    rw [hc, h.pos, h.dir]
    rfl
  · simp only [LangtonsAnt.step, hc, h.dir]
  · intro p hp
    simp only [LangtonsAnt.step, flip, h.pos, h.board p hp]

theorem RegionEq.run {R : Point -> Prop} {s t : State}
    (h : RegionEq R s t) (n : Nat) (hb : forall j, j < n -> R (run t j).pos) :
    RegionEq R (run s n) (run t n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact (ih (fun j hj => hb j (by omega))).step (hb n (by omega))

theorem region_shift_future {R : Point -> Prop} {s : State} {q : Nat} {v : Point}
    (he : RegionEq R (run s q) (translate v s))
    (hb : forall n, R (run (translate v s) n).pos) :
    forall n, (run s (n + q)).pos = addPoint v (run s n).pos /\
      readColor s (n + q) = readColor s n := by
  intro n
  have hh := he.run n (fun j _ => hb j)
  have hc : readColor (run s q) n = readColor (translate v s) n := by
    unfold readColor
    rw [hh.pos]
    exact hh.board _ (hb n)
  constructor
  · rw [Nat.add_comm n q, run_add]
    rw [hh.pos, translate_run]
    rfl
  · rw [translate_readColor] at hc
    simpa only [readColor, Nat.add_comm n q, run_add] using hc

theorem frontier_collision_not_least {R : Point -> Prop} {s : State}
    {P q : Nat} {m a : Int} {v : Point}
    (hq : 0 < q) (ha : 0 <= a) (ham : a < m) (hv : v.1 = a)
    (he : RegionEq R (run s q) (translate v s))
    (hb : forall n, R (run (translate v s) n).pos)
    (hp : forall n, (run s (n + P)).pos.1 = (run s n).pos.1 + m) :
    Not (RootWord.LeastReadPeriod P (readColor s)) := by
  intro hleast
  have hf := region_shift_future he hb
  have htail : forall n, 0 <= n ->
      (run s (n + q)).pos.1 = (run s n).pos.1 + a := by
    intro n _
    have hh := congrArg Prod.fst (hf n).1
    simpa only [addPoint, hv, Int.add_comm] using hh
  have hh := RootTail.tail_drift_bounds_root (N := 0)
    (x := fun n => (run s n).pos.1) hleast hq ha
    (fun n _ => (hf n).2) hp htail
  omega

theorem diagonal_tail_alignment {P q N : Nat} {x y : Nat -> Int} {m a b : Int}
    (hP : 0 < P)
    (hx : forall n, x (n + P) = x n + m)
    (hy : forall n, y (n + P) = y n - m)
    (hax : forall n, N <= n -> x (n + q) = x n + a)
    (hby : forall n, N <= n -> y (n + q) = y n + b) : b = -a := by
  have hy' : forall n, y (n + P) = y n + (-m) := by
    intro n
    simpa only [Int.sub_eq_add_neg] using hy n
  have rx := RootTail.shifts_commensurate hx (RootTail.shift_of_eventual hP hx hax)
  have ry := RootTail.shifts_commensurate hy' (RootTail.shift_of_eventual hP hy' hby)
  rw [Int.mul_neg, rx] at ry
  apply Int.eq_of_mul_eq_mul_left (a := (P : Int)) (by omega)
  rw [Int.mul_neg]
  exact ry.symm

noncomputable def trimFuture (s : State) : State := by
  classical
  exact { board := fun p => if exists n, (run s n).pos = p then s.board p else false
          pos := s.pos, dir := s.dir }

theorem trimFuture_trace (s : State) (n : Nat) :
    (run (trimFuture s) n).pos = (run s n).pos /\
    (run (trimFuture s) n).dir = (run s n).dir /\
    readColor (trimFuture s) n = readColor s n := by
  classical
  let R : Point -> Prop := fun p => exists j, (run s j).pos = p
  have he : RegionEq R (trimFuture s) s := by
    refine { pos := rfl, dir := rfl, board := ?_ }
    intro p hp
    change (if exists j, (run s j).pos = p then s.board p else false) = s.board p
    exact ite_eq_left hp
  have hh := he.run n (fun j _ => Exists.intro j rfl)
  refine And.intro hh.pos (And.intro hh.dir ?_)
  unfold readColor
  rw [hh.pos]
  exact hh.board _ (Exists.intro n rfl)

theorem board_before_visit (s : State) (p : Point) (n : Nat)
    (h : forall j, j < n -> Not ((run s j).pos = p)) :
    (run s n).board p = s.board p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change flip (run s n).board (run s n).pos p = _
    rw [flip_other _ (Ne.symm (h n (by omega)))]
    exact ih (fun j hj => h j (by omega))

theorem initial_color_forced {s t : State} {n : Nat} {p : Point}
    (hpos : forall j, (run s j).pos = (run t j).pos)
    (hread : readColor s n = readColor t n)
    (hvisit : (run s n).pos = p)
    (hfirst : forall j, j < n -> Not ((run s j).pos = p)) :
    s.board p = t.board p := by
  have hs := board_before_visit s p n hfirst
  have ht := board_before_visit t p n (fun j hj => by rw [<- hpos j]; exact hfirst j hj)
  have hv : (run t n).pos = p := (hpos n).symm.trans hvisit
  simpa only [readColor, hvisit, hv, hs, ht] using hread

end LangtonsAnt.FrontierCollision

