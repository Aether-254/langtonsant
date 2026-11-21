import HardPhaseRecovery

/-!
# Phase 49: a parallel northeast highway

Flipping the current cell at the mature first-visit phase 49 does not recover locally.
Exploration (not a proof dependency) showed that the ant builds a *parallel* highway heading
northeast, at `x - y ≈ 76`, instead of walking back along the old trail.

The old highway and its whole history lie in the narrow diagonal strip `-2 <= x - y <= 8`.
`TrailAgreement cut s t` asks two states to agree everywhere except possibly inside that strip
above the weight `cut`.  The proof shows:

* one kernel-checked prefix of 52421 steps (history length 13 periods) only reads cells with
  `x + y <= 0` or outside the strip, and ends in a southward standard entry;
* the resulting northeast highway keeps `x - y` in `[68, 78]` forever, because its drift
  `(2,2)` preserves `x - y` and the seed path has `x - y ∈ [-2, 8]`;
* longer seed histories, and more generally any history that differs from the seed only inside
  the strip above weight 0, change no cell the trajectory ever reads.

Unlike the other 21 phases, the hypothesis is `TrailAgreement 0`, not `AgreesBelow 0`: the new
highway crosses `x + y > 0`, so arbitrary colors there are *not* allowed.
-/

namespace LangtonsAnt

def trailCross (p : Point) : Int := p.1 - p.2

def TrailStrip (p : Point) : Prop := -2 <= trailCross p ∧ trailCross p <= 8

instance (p : Point) : Decidable (TrailStrip p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def TrailSafe (p : Point) : Prop := weight p <= 0 ∨ ¬TrailStrip p

instance (p : Point) : Decidable (TrailSafe p) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Agreement of pose and of the board outside the strip part above `cut`. -/
structure TrailAgreement (cut : Int) (s t : State) : Prop where
  pos : s.pos = t.pos
  dir : s.dir = t.dir
  board : forall p, weight p <= cut ∨ ¬TrailStrip p -> s.board p = t.board p

theorem TrailAgreement.refl (cut : Int) (s : State) : TrailAgreement cut s s :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem TrailAgreement.trans {cut : Int} {s t u : State}
    (h : TrailAgreement cut s t) (g : TrailAgreement cut t u) : TrailAgreement cut s u :=
  ⟨h.pos.trans g.pos, h.dir.trans g.dir, fun p hp => (h.board p hp).trans (g.board p hp)⟩

theorem TrailAgreement.weaken {a b : Int} {s t : State}
    (h : TrailAgreement a s t) (hab : b <= a) : TrailAgreement b s t := by
  refine ⟨h.pos, h.dir, fun p hp => h.board p ?_⟩
  rcases hp with hp | hp
  · exact Or.inl (by omega)
  · exact Or.inr hp

theorem TrailAgreement.toAgreesBelow {cut : Int} {s t : State}
    (h : TrailAgreement cut s t) : AgreesBelow cut s t :=
  ⟨h.pos, h.dir, fun p hp => h.board p (Or.inl hp)⟩

theorem TrailAgreement.step {cut : Int} {s t : State}
    (h : TrailAgreement cut s t) (hp : weight t.pos <= cut ∨ ¬TrailStrip t.pos) :
    TrailAgreement cut (step s) (step t) := by
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

theorem TrailAgreement.run {cut : Int} {s t : State}
    (h : TrailAgreement cut s t) (n : Nat)
    (hb : forall j, j < n -> weight (run t j).pos <= cut ∨ ¬TrailStrip (run t j).pos) :
    TrailAgreement cut (run s n) (run t n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact (ih (fun j hj => hb j (by omega))).step (hb n (by omega))

theorem TrailAgreement.flip {cut : Int} {s t : State} (h : TrailAgreement cut s t) :
    TrailAgreement cut (flipCell s s.pos) (flipCell t t.pos) := by
  refine ⟨h.pos, h.dir, ?_⟩
  intro p hp
  simp only [flipCell, LangtonsAnt.flip, h.pos, h.board p hp]

/-- Transfer a standard highway along a strip agreement whose reference never reads the strip
part above `cut`. -/
theorem StandardHighwayFrom.of_trailAgreement {cut : Int} {s t : State} {T : Nat} {v : Point}
    (h : StandardHighwayFrom t T v) (hm : TrailAgreement cut s t)
    (hb : forall n, weight (run t n).pos <= cut ∨ ¬TrailStrip (run t n).pos) :
    StandardHighwayFrom s T v := by
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

/-- A diagonal translation preserves the strip coordinate. -/
theorem trailCross_offset (k : Nat) (p : Point) :
    trailCross (addPoint (offset (-2, -2) k) p) = trailCross p := by
  rw [southwest_offset]
  simp only [trailCross, addPoint]
  omega

/-! ## The seed path stays in the strip, and the seed board is white outside it -/

def checkTrailRegion (guard : Point -> Bool) : Nat -> FiniteState -> Bool
  | 0, _ => true
  | n + 1, s => guard s.pos && checkTrailRegion guard n s.step

theorem checkTrailRegion_sound {guard : Point -> Bool} {n : Nat} {s : FiniteState}
    (h : checkTrailRegion guard n s = true) :
    forall j, j < n -> guard (run s.toState j).pos = true := by
  induction n generalizing s with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkTrailRegion, Bool.and_eq_true] at h
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j =>
      have hh := ih h.2 j (by omega)
      rw [FiniteState.toState_step] at hh
      change guard (run (run s.toState 1) j).pos = true at hh
      rw [← run_add] at hh
      simpa only [Nat.add_comm 1 j] using hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem trail_cycle_strip_check :
    checkTrailRegion (fun p => decide (TrailStrip p)) 104 highwaySeed = true := by
  decide +kernel

theorem trail_seed_black_strip :
    forall p, p ∈ highwaySeed.black -> TrailStrip p := by
  have h : highwaySeed.black.all (fun p => decide (TrailStrip p)) = true := by
    decide +kernel
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

theorem trail_seed_run_strip (n : Nat) : TrailStrip (run highwaySeed.toState n).pos := by
  obtain ⟨q, j, hj, rfl⟩ : exists q j, j < 104 ∧ n = 104 * q + j :=
    ⟨n / 104, n % 104, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 104).symm⟩
  have hp := (highwaySeed_certificate.block_prefix q j (by omega)).pos
  have hc := of_decide_eq_true (checkTrailRegion_sound trail_cycle_strip_check j hj)
  change _ = addPoint (offset (-2, -2) q) (run highwaySeed.toState j).pos at hp
  rw [hp]
  unfold TrailStrip
  rw [trailCross_offset]
  exact hc

theorem trail_seed_run_white {p : Point} (hp : ¬TrailStrip p) (n : Nat) :
    (run highwaySeed.toState n).board p = false := by
  rw [board_unchanged_of_avoids highwaySeed.toState p n (by
    intro j _ he
    exact hp (he ▸ trail_seed_run_strip j))]
  change decide (p ∈ highwaySeed.black) = false
  exact decide_eq_false (fun hm => hp (trail_seed_black_strip p hm))

/-! ## The finite recovery prefix, checked in a rotated and translated frame -/

def trailFlipTime : Nat := 104 * 13 + 49
def trailDelay : Nat := 52421

/-- Translate, then rotate by a half turn, so that the whole computation fits the box. -/
def trailFrame (s : State) : State := rotateState .south (translate (8, 16) s)

def trailUnframePoint (p : Point) : Point := subPoint (rotatePoint .south p) (8, 16)

theorem trailFrame_run (s : State) (n : Nat) :
    run (trailFrame s) n = trailFrame (run s n) := by
  simp only [trailFrame, rotate_run, translate_run]

theorem trailUnframe_pos (s : State) : trailUnframePoint (trailFrame s).pos = s.pos := by
  apply Prod.ext <;>
    simp only [trailUnframePoint, trailFrame, rotateState, translate, rotatePoint, addPoint,
      subPoint] <;> omega

theorem trailFrame_back (s : State) :
    translate (-8, -16) (rotateState .south (trailFrame s)) = s := by
  have hr : rotateState .south (rotateState .south (translate (8, 16) s)) =
      translate (8, 16) s := inverse_rotateState .south _
  simp only [trailFrame, hr, translate_add]
  have hz : addPoint ((-8, -16) : Point) (8, 16) = (0, 0) := by decide
  rw [hz, translate_zero]

def trailPackedInput : FiniteState :=
  ((flippedAt trailFlipTime).translate (8, 16)).rotate .south

def trailPackedTarget : FiniteState := highwaySeed.translate (-47, 21)

/-- Check a finite prefix (box and guard at every step) and the final entry in one pass. -/
def checkTrailPrefix (guard : Point -> Bool) (cut : Int) (target : FiniteState) :
    Nat -> PackedState -> Bool
  | 0, s => checkPackedAgreement cut s target
  | n + 1, s => decide (InBox s.pos) && guard s.pos &&
      checkTrailPrefix guard cut target n s.step

theorem checkTrailPrefix_sound {guard : Point -> Bool} {cut : Int}
    {target : FiniteState} {n : Nat} {s : PackedState}
    (h : checkTrailPrefix guard cut target n s = true) :
    (forall j, j < n -> guard (run s.toState j).pos = true) ∧
      AgreesBelow cut (run s.toState n) target.toState := by
  induction n generalizing s with
  | zero => exact ⟨fun j hj => by omega, checkPackedAgreement_sound h⟩
  | succ n ih =>
    simp only [checkTrailPrefix, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, he⟩ := ih h.2
    have hs := PackedState.toState_step s h.1.1
    rw [hs] at hb he
    have hr : forall j, run (step s.toState) j = run s.toState (j + 1) := by
      intro j
      change run (run s.toState 1) j = _
      rw [← run_add, Nat.add_comm 1 j]
    refine ⟨?_, ?_⟩
    · intro j hj
      cases j with
      | zero => exact h.1.2
      | succ j => simpa only [hr] using hb j (by omega)
    · simpa only [hr] using he

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem trail_input_inBox_check :
    trailPackedInput.black.all (fun p => decide (InBox p)) = true := by
  decide +kernel

theorem trailPackedInput_toState : trailPackedInput.toPacked.toState =
    trailFrame (flippedAt trailFlipTime).toState := by
  rw [FiniteState.toPacked_toState _ (fun p hp =>
    of_decide_eq_true (List.all_eq_true.mp trail_input_inBox_check p hp))]
  simp only [trailPackedInput, FiniteState.toState_rotate, FiniteState.toState_translate,
    trailFrame]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem trail_prefix_check :
    checkTrailPrefix (fun p => decide (TrailSafe (trailUnframePoint p))) (-26)
      trailPackedTarget trailDelay trailPackedInput.toPacked = true := by
  decide +kernel

abbrev trailStart : State := (flippedAt trailFlipTime).toState

theorem trail_prefix :
    (forall j, j < trailDelay -> TrailSafe (run trailStart j).pos) ∧
      AgreesBelow (weight ((-47, 21) : Point)) (run (trailFrame trailStart) trailDelay)
        (translate (-47, 21) highwaySeed.toState) := by
  have h := checkTrailPrefix_sound trail_prefix_check
  rw [trailPackedInput_toState] at h
  refine ⟨?_, ?_⟩
  · intro j hj
    have hh := of_decide_eq_true (h.1 j hj)
    rw [trailFrame_run, trailUnframe_pos] at hh
    exact hh
  · have he := h.2
    rw [trailPackedTarget, FiniteState.toState_translate] at he
    exact he

/-! ## The northeast highway and its permanent distance from the strip -/

theorem trail_standard : StandardHighwayFrom trailStart trailDelay (2, 2) := by
  have hF := standard_highway_of_entry (-47, 21) trail_prefix.2
  have hR := (hF.rotate .south).translate (-8, -16)
  rw [trailFrame_back] at hR
  exact hR

theorem trail_tail_pos (m : Nat) :
    (run trailStart (trailDelay + m)).pos =
      (39 - (run highwaySeed.toState m).pos.1, -37 - (run highwaySeed.toState m).pos.2) := by
  have hc := highwaySeed_certificate.translate (-47, 21)
  have he : AgreesBelow (0 + weight ((-47, 21) : Point)) (run (trailFrame trailStart) trailDelay)
      (translate (-47, 21) highwaySeed.toState) := by
    simpa only [Int.zero_add] using trail_prefix.2
  have hm := hc.matches_forever he m
  rw [← run_add, translate_run, trailFrame_run] at hm
  have hp := hm.pos
  have hu := trailUnframe_pos (run trailStart (trailDelay + m))
  rw [hp] at hu
  rw [← hu]
  apply Prod.ext <;>
    simp only [trailUnframePoint, translate, rotatePoint, addPoint, subPoint] <;> omega

theorem trail_all_safe (n : Nat) : TrailSafe (run trailStart n).pos := by
  by_cases hn : n < trailDelay
  · exact trail_prefix.1 n hn
  · obtain ⟨m, rfl⟩ : exists m, n = trailDelay + m := ⟨n - trailDelay, by omega⟩
    right
    have hs := trail_seed_run_strip m
    rw [trail_tail_pos]
    simp only [TrailStrip, trailCross] at hs ⊢
    omega

/-! ## Every history agreeing with the seed off the strip -/

theorem seed_trail_agreement (k : Nat) :
    TrailAgreement (weight (offset (-2, -2) k))
      (run highwaySeed.toState (104 * k + trailFlipTime))
      (translate (offset (-2, -2) k) (run highwaySeed.toState trailFlipTime)) := by
  let v := offset (-2, -2) k
  have hm := highwaySeed_certificate.matches_forever (AgreesBelow.refl 0 highwaySeed.toState)
    (104 * k)
  have hp := highwaySeed_certificate.blocks k
  have hv : weight v <= 0 := offset_nonpos (by decide) k
  have he : AgreesBelow (weight v) (run highwaySeed.toState (104 * k))
      (translate v highwaySeed.toState) :=
    (hm.weaken hv).trans (by simpa only [Int.zero_add] using hp)
  have hg := he.run trailFlipTime (by
    intro j _
    rw [translate_run]
    change weight (addPoint v (run highwaySeed.toState j).pos) <= _
    rw [weight_addPoint]
    have hb := highwaySeed_certificate.all_bounded j
    omega)
  rw [← run_add, translate_run] at hg
  refine ⟨hg.pos, hg.dir, ?_⟩
  intro p hp
  rcases hp with hp | hp
  · exact hg.board p hp
  · have htb : forall (t : State) (q : Point), (translate v t).board q = t.board (subPoint q v) :=
      fun _ _ => rfl
    rw [trail_seed_run_white hp, htb]
    have hq : ¬TrailStrip (subPoint p v) := by
      intro hs
      apply hp
      have hc : trailCross p = trailCross (subPoint p v) := by
        have h0 := trailCross_offset k (subPoint p v)
        have h1 : addPoint v (subPoint p v) = p := by
          apply Prod.ext <;> simp [addPoint, subPoint] <;> omega
        rw [h1] at h0
        exact h0
      unfold TrailStrip at hs ⊢
      rw [hc]
      exact hs
    rw [trail_seed_run_white hq]

/-- Phase-49 recovery for every history that agrees with the seed off the strip above weight 0,
after any number `k` of further periods. -/
theorem phase_forty_nine_recovers {s : State} (h : TrailAgreement 0 s highwaySeed.toState)
    (k : Nat) :
    StandardHighwayFrom
      (flipCell (run s (104 * k + trailFlipTime)) (run s (104 * k + trailFlipTime)).pos)
      trailDelay (2, 2) := by
  let v := offset (-2, -2) k
  have hv : weight v <= 0 := offset_nonpos (by decide) k
  have h1 : TrailAgreement 0 (run s (104 * k + trailFlipTime))
      (run highwaySeed.toState (104 * k + trailFlipTime)) :=
    h.run _ (fun j _ => Or.inl (highwaySeed_certificate.all_bounded j))
  have h3 := ((h1.weaken hv).trans (seed_trail_agreement k)).flip
  have hflip : flipCell (translate v (run highwaySeed.toState trailFlipTime))
      (translate v (run highwaySeed.toState trailFlipTime)).pos = translate v trailStart := by
    change flipCell (translate v (run highwaySeed.toState trailFlipTime))
      (addPoint v (run highwaySeed.toState trailFlipTime).pos) = _
    rw [flipCell_translate, trailStart, flippedAt_toState]
  rw [hflip] at h3
  apply (trail_standard.translate v).of_trailAgreement h3
  intro n
  rw [translate_run]
  change weight (addPoint v (run trailStart n).pos) <= _ ∨
    ¬TrailStrip (addPoint v (run trailStart n).pos)
  rcases trail_all_safe n with hw | hs
  · left
    rw [weight_addPoint]
    omega
  · right
    unfold TrailStrip
    rw [trailCross_offset]
    exact hs

theorem phase_forty_nine_seed (k : Nat) :
    EventuallyStandard
      (flipCell (run highwaySeed.toState (104 * k + trailFlipTime))
        (run highwaySeed.toState (104 * k + trailFlipTime)).pos) :=
  ⟨trailDelay, (2, 2), diagonal_rotated_southwest .south,
    phase_forty_nine_recovers (TrailAgreement.refl 0 _) k⟩

/-! ## All 22 first-visit phases -/

/-- Every mature first-visit phase of the seed highway recovers, for every history that agrees
with the seed outside the trail strip above weight 0 (in particular for the seed's own history),
and after any number of further periods. -/
theorem all_fresh_phases_recover (phi : Nat) (hphi : phi ∈ freshPhases) :
    exists H : Nat, forall s : State, TrailAgreement 0 s highwaySeed.toState -> forall k : Nat,
      EventuallyStandard
        (flipCell (run s (104 * (k + H) + phi)) (run s (104 * (k + H) + phi)).pos) := by
  by_cases h49 : phi = 49
  · subst h49
    refine ⟨13, fun s h k => ?_⟩
    have e : 104 * (k + 13) + 49 = 104 * k + trailFlipTime := by
      unfold trailFlipTime
      omega
    rw [e]
    exact ⟨trailDelay, (2, 2), diagonal_rotated_southwest .south, phase_forty_nine_recovers h k⟩
  · obtain ⟨H, hH⟩ := fresh_phase_recovers_except_49 phi hphi h49
    exact ⟨H, fun s h k => hH s h.toAgreesBelow k⟩

end LangtonsAnt
