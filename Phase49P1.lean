import TrailRetrace
import SingleBlackLate
import SingleBlackCover
import Phase49Data

/-!
# Phase 49 on the blank orbit

On the blank orbit a phase-49 flip builds the northeast highway of `TrailRetrace.lean`, which
then runs into the blank remnants above weight 0 and finally leaves as a northwest highway.
Write `s0` for the normalized blank state at its entry (time 12080), and
`F_k = flip (run s0 (104*k + trailFlipTime))`, the phase-49 flip after `13 + k` periods.

1. `s0` is the seed perturbed by a finite mask `junk49` lying in `x + y > 0` (kernel check of the
   blank run).
2. The seed-history reference `B_k = translate v_k trailStart` never reads a junk cell before the
   aligned time `t_k = trailDelay + 104*(14 + k)` (finite checks: the prefix, and the lane cells).
3. Hence `run F_k t_k` agrees on the half-plane `U = {58 <= x + y}` with one concrete state `Y`,
   the northeast-highway template at period 14 overlaid with the junk, for every `k`.
4. `Y` is run once (kernel check): it stays in `U` and enters a standard highway heading east
   (drift `(-2,2)`); its tail keeps `x + y` in `[93, 103]`, so it stays in `U` forever.

Therefore every `F_k` is eventually standard, which completes the late single-black theorem.
-/

namespace LangtonsAnt


/-! ## Agreement on an arbitrary region -/

structure RegionAgree (R : Point -> Prop) (s t : State) : Prop where
  pos : s.pos = t.pos
  dir : s.dir = t.dir
  board : forall p, R p -> s.board p = t.board p

theorem RegionAgree.step {R : Point -> Prop} {s t : State}
    (h : RegionAgree R s t) (hp : R t.pos) : RegionAgree R (step s) (step t) := by
  have hc : s.board s.pos = t.board t.pos := by
    rw [h.pos]
    exact h.board _ hp
  refine ⟨?_, ?_, ?_⟩
  · change move s.pos (turn (s.board s.pos) s.dir) = _
    rw [hc, h.pos, h.dir]
    rfl
  · simp only [LangtonsAnt.step, hc, h.dir]
  · intro p hp
    simp only [LangtonsAnt.step, flip, h.pos, h.board p hp]

theorem RegionAgree.run {R : Point -> Prop} {s t : State}
    (h : RegionAgree R s t) (n : Nat) (hb : forall j, j < n -> R (run t j).pos) :
    RegionAgree R (run s n) (run t n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact (ih (fun j hj => hb j (by omega))).step (hb n (by omega))

theorem RegionAgree.mono {R R' : Point -> Prop} {s t : State}
    (h : RegionAgree R s t) (hsub : forall p, R' p -> R p) : RegionAgree R' s t :=
  ⟨h.pos, h.dir, fun p hp => h.board p (hsub p hp)⟩

theorem RegionAgree.trans {R : Point -> Prop} {s t u : State}
    (h : RegionAgree R s t) (g : RegionAgree R t u) : RegionAgree R s u :=
  ⟨h.pos.trans g.pos, h.dir.trans g.dir, fun p hp => (h.board p hp).trans (g.board p hp)⟩

theorem RegionAgree.perturb {R : Point -> Prop} {s t : State}
    (h : RegionAgree R s t) (mask : Board) :
    RegionAgree R (LangtonsAnt.perturb mask s) (LangtonsAnt.perturb mask t) := by
  refine ⟨h.pos, h.dir, ?_⟩
  intro p hp
  change (s.board p ^^ mask p) = (t.board p ^^ mask p)
  rw [h.board p hp]

theorem RegionAgree.translate {R : Point -> Prop} {s t : State}
    (h : RegionAgree R s t) (v : Point) :
    RegionAgree (fun p => R (subPoint p v)) (LangtonsAnt.translate v s)
      (LangtonsAnt.translate v t) := by
  refine ⟨congrArg (addPoint v) h.pos, h.dir, ?_⟩
  intro p hp
  exact h.board _ hp

theorem StandardHighwayFrom.of_regionAgree {R : Point -> Prop} {s t : State} {T : Nat}
    {v : Point} (h : StandardHighwayFrom t T v) (hm : RegionAgree R s t)
    (hb : forall n, R (run t n).pos) : StandardHighwayFrom s T v := by
  have htrace : forall n,
      (run s n).pos = (run t n).pos ∧ (run s n).dir = (run t n).dir ∧
      readColor s n = readColor t n := by
    intro n
    have hh := hm.run n (fun j _ => hb j)
    refine ⟨hh.pos, hh.dir, ?_⟩
    unfold readColor
    rw [hh.pos]
    exact hh.board _ (hb n)
  refine ⟨?_, ?_⟩
  · intro n hn
    have h0 := htrace n
    have h1 := htrace (n + 104)
    simpa only [h0.1, h0.2.1, h1.1, h1.2.1] using h.1 n hn
  · intro n
    exact (htrace (T + n)).2.2.trans (h.2 n)

/-! ## Frames -/

theorem rotateState_translate (r : Direction) (v : Point) (s : State) :
    rotateState r (LangtonsAnt.translate v s) =
      LangtonsAnt.translate (rotatePoint r v) (rotateState r s) := by
  have hb : (fun p => s.board (subPoint (rotatePoint (inverseRotation r) p) v)) =
      fun p => s.board (rotatePoint (inverseRotation r) (subPoint p (rotatePoint r v))) := by
    funext p
    congr 1
    cases r <;> apply Prod.ext <;>
      simp [subPoint, rotatePoint, inverseRotation] <;> omega
  simp only [rotateState, LangtonsAnt.translate, hb, rotatePoint_add]

def unframeS (s : State) : State := LangtonsAnt.translate (-8, -16) (rotateState .south s)

theorem unframeS_trailFrame (s : State) : unframeS (trailFrame s) = s := trailFrame_back s

theorem AgreesBelow.unframe {cut : Int} {X Y : State} (h : AgreesBelow cut X Y) :
    RegionAgree (fun p => -24 - cut <= weight p) (unframeS X) (unframeS Y) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [unframeS, LangtonsAnt.translate, rotateState, h.pos]
  · simp only [unframeS, LangtonsAnt.translate, rotateState, h.dir]
  · intro p hp
    simp only [unframeS, LangtonsAnt.translate, rotateState]
    apply h.board
    simp only [weight, subPoint, rotatePoint, inverseRotation] at hp ⊢
    omega

/-! ## 1. The blank state at its entry is the seed plus a finite junk mask -/

def junkMask : Board := fun p => decide (p ∈ junk49)

theorem junk49_weight_check : junk49.all (fun p => decide (0 < weight p)) = true := by
  decide +kernel

theorem junk49_weight {p : Point} (hp : p ∈ junk49) : 0 < weight p :=
  of_decide_eq_true (List.all_eq_true.mp junk49_weight_check p hp)

theorem junkMask_of_weight {p : Point} (hw : weight p <= 0) : junkMask p = false := by
  unfold junkMask
  exact decide_eq_false (fun hm => by have := junk49_weight hm; omega)

def wideRun : Nat -> WideState -> Option WideState
  | 0, s => some s
  | n + 1, s => if InWide s.pos then wideRun n s.step else none

theorem wideRun_sound {n : Nat} {s t : WideState} (h : wideRun n s = some t) :
    t.toState = run s.toState n := by
  induction n generalizing s with
  | zero =>
    have heq : s = t := by simpa [wideRun] using h
    exact congrArg WideState.toState heq.symm
  | succ n ih =>
    by_cases hp : InWide s.pos
    · simp only [wideRun, hp, ite_true] at h
      have hh := ih h
      rw [WideState.toState_step _ hp] at hh
      change t.toState = run (run s.toState 1) n at hh
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 n] using hh
    · simp [wideRun, hp] at h

def blankAbsCells : List Point :=
  (highwaySeed.black ++ junk49).map (fun q => (q.1 - 56, q.2 - 30))

def checkBlankJunk : Bool :=
  match wideRun 12080 wideBlank with
  | none => false
  | some t => (t.pos == (-56, -30)) && (t.dir == .north) &&
      blankAbsCells.all (fun p => decide (InWide p)) && (t.bits == wideCells blankAbsCells)


end LangtonsAnt
