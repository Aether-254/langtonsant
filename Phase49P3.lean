import Phase49K2

namespace LangtonsAnt

theorem trail_prefix_avoid (j : Nat) (hj : j < trailDelay) : avoidJunk2 (run trailStart j).pos = true :=
  trail_prefix_avoid2 j hj

def laneHit (x c : Point) : Bool :=
  let a := x.1 - 39 + c.1
  let b := x.2 + 37 + c.2
  decide (a = b) && decide (a % 2 = 0) && decide (a < 28)

theorem lane_check : junk49.all (fun x => cycleTable.all (fun c => !laneHit x c)) = true := by
  decide +kernel

theorem cyclePos_mem_check : forall i : Fin 104, cyclePos i.val ∈ cycleTable := by
  decide +kernel

theorem cyclePos_mem {i : Nat} (hi : i < 104) : cyclePos i ∈ cycleTable :=
  cyclePos_mem_check ⟨i, hi⟩

/-- The aligned time: the northeast highway at period 14 of the base frame. -/
def align49 (k : Nat) : Nat := trailDelay + 104 * (14 + k)

theorem ref49_avoids_junk (k t : Nat) (ht : t < align49 k) :
    junkMask (run (ref49 k) t).pos = false := by
  unfold ref49
  rw [translate_run]
  change junkMask (addPoint (offset (-2, -2) k) (run trailStart t).pos) = false
  by_cases hp : t < trailDelay
  · exact avoidJunk2_sound (trail_prefix_avoid t hp) k
  · obtain ⟨n, rfl⟩ : exists n, t = trailDelay + n := ⟨t - trailDelay, by omega⟩
    obtain ⟨j, i, hi, rfl⟩ : exists j i, i < 104 ∧ n = 104 * j + i :=
      ⟨n / 104, n % 104, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 104).symm⟩
    have hj : j < 14 + k := by unfold align49 at ht; omega
    rw [trail_tail_pos, seed_pos_decomp j i hi, southwest_offset]
    unfold junkMask
    apply decide_eq_false
    intro hm
    have hc := List.all_eq_true.mp (List.all_eq_true.mp lane_check _ hm) _ (cyclePos_mem hi)
    simp only [laneHit, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
    simp only [addPoint] at hc
    omega

/-! ## 4. The reference at the aligned time is the northeast-highway template -/

def tmpl49 (j : Nat) : State :=
  unframeS (LangtonsAnt.translate (offset (-2, -2) j)
    (LangtonsAnt.translate (-47, 21) highwaySeed.toState))

theorem tmpl49_eq (j : Nat) :
    tmpl49 j = LangtonsAnt.translate (2 * (j : Int) + 39, 2 * (j : Int) - 37)
      (rotateState .south highwaySeed.toState) := by
  unfold tmpl49 unframeS
  rw [translate_add, rotateState_translate, translate_add, southwest_offset]
  congr 1
  apply Prod.ext <;> simp [addPoint, rotatePoint] <;> omega

theorem trail_run_tmpl (j : Nat) :
    RegionAgree (fun p => 2 + 4 * (j : Int) <= weight p)
      (run trailStart (trailDelay + 104 * j)) (tmpl49 j) := by
  have hc := highwaySeed_certificate.translate (-47, 21)
  have he : AgreesBelow (0 + weight ((-47, 21) : Point)) (run (trailFrame trailStart) trailDelay)
      (LangtonsAnt.translate (-47, 21) highwaySeed.toState) := by
    simpa only [Int.zero_add] using trail_prefix.2
  have hm := hc.matches_forever he (104 * j)
  have hb := hc.blocks j
  have hv : weight (offset (-2, -2) j) <= 0 := offset_nonpos (by decide) j
  have hab := (hm.weaken (by omega)).trans hb
  rw [← run_add, trailFrame_run] at hab
  have hu := hab.unframe
  rw [unframeS_trailFrame] at hu
  apply hu.mono
  intro p hp
  have hw : weight (offset (-2, -2) j) = -4 * (j : Int) := by
    rw [southwest_offset]; simp [weight]; omega
  rw [hw]
  simp only [weight] at hp ⊢
  omega

/-- The comparison half-plane. -/
def U49 (p : Point) : Prop := 58 <= weight p

theorem ref49_tmpl (k : Nat) :
    RegionAgree U49 (run (ref49 k) (align49 k)) (tmpl49 14) := by
  have h := (trail_run_tmpl (14 + k)).translate (offset (-2, -2) k)
  have hs : LangtonsAnt.translate (offset (-2, -2) k) (tmpl49 (14 + k)) = tmpl49 14 := by
    rw [tmpl49_eq, tmpl49_eq, translate_add, southwest_offset]
    congr 1
    apply Prod.ext <;> simp [addPoint] <;> omega
  rw [hs, ← translate_run] at h
  unfold ref49 align49
  apply h.mono
  intro p hp
  simp only [U49, weight, subPoint] at hp ⊢
  rw [southwest_offset]
  simp only
  omega

/-! ## 5. Every aligned flipped blank state agrees with one concrete state above weight 58 -/

def Y49 : State := perturb junkMask (tmpl49 14)

theorem flip49_blank_U (k : Nat) :
    RegionAgree U49 (run (flip49 blankEntryState k) (align49 k)) Y49 := by
  have hpos : forall j, j < align49 k ->
      junkMask (run (flip49 highwaySeed.toState k) j).pos = false := by
    intro j hj
    rw [(flip49_seed_ref_run k j).pos]
    exact ref49_avoids_junk k j hj
  rw [flip49_blank, run_perturb_avoids _ _ _ hpos]
  have h1 := ((flip49_seed_ref_run k (align49 k)).perturb junkMask).mono
    (R' := U49) (fun p hp => Or.inr (Or.inr (by simp only [U49] at hp; omega)))
  exact h1.trans ((ref49_tmpl k).perturb junkMask)

/-! ## 6. The concrete state `Y49`: one checked run and its permanent tail -/

def xorList (a b : List Point) : List Point :=
  a.filter (fun p => !decide (p ∈ b)) ++ b.filter (fun p => !decide (p ∈ a))

theorem mem_xorList (a b : List Point) (p : Point) :
    decide (p ∈ xorList a b) = (decide (p ∈ a) ^^ decide (p ∈ b)) := by
  by_cases ha : p ∈ a <;> by_cases hb : p ∈ b <;> simp [xorList, ha, hb]

def tmplFS : FiniteState := (highwaySeed.rotate .south).translate (67, -9)

def Y49FS : FiniteState := { tmplFS with black := xorList tmplFS.black junk49 }

theorem tmplFS_toState : tmplFS.toState = tmpl49 14 := by
  rw [tmpl49_eq, tmplFS, FiniteState.toState_translate, FiniteState.toState_rotate]
  rfl

theorem Y49FS_toState : Y49FS.toState = Y49 := by
  unfold Y49
  rw [← tmplFS_toState]
  have hb : (fun p => decide (p ∈ Y49FS.black)) =
      fun p => decide (p ∈ tmplFS.black) ^^ junkMask p := by
    funext p
    exact mem_xorList tmplFS.black junk49 p
  show (⟨fun p => decide (p ∈ Y49FS.black), Y49FS.pos, Y49FS.dir⟩ : State) =
    perturb junkMask tmplFS.toState
  rw [hb]
  rfl

/-- The frame used for the wide-window run: translate by `(-56,-30)`, rotate by `west`. -/
def Y49Frame : FiniteState := (Y49FS.translate (-56, -30)).rotate .west

def checkWideGuardEntry (guard : Point -> Bool) (cut : Int) (target : FiniteState) :
    Nat -> WideState -> Bool
  | 0, s => checkWideAgreement cut s target
  | n + 1, s => decide (InWide s.pos) && guard s.pos && checkWideGuardEntry guard cut target n s.step

theorem checkWideGuardEntry_sound {guard : Point -> Bool} {cut : Int} {target : FiniteState}
    {n : Nat} {s : WideState} (h : checkWideGuardEntry guard cut target n s = true) :
    (forall j, j < n -> guard (run s.toState j).pos = true) ∧
      AgreesBelow cut (run s.toState n) target.toState := by
  induction n generalizing s with
  | zero => exact ⟨fun j hj => by omega, checkWideAgreement_sound h⟩
  | succ n ih =>
    simp only [checkWideGuardEntry, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, he⟩ := ih h.2
    have hs := WideState.toState_step s h.1.1
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

def y49Guard (fp : Point) : Bool := decide (58 <= fp.2 - fp.1 + 86)

def y49Delay : Nat := 8603

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem y49_frame_inWide_check : Y49Frame.black.all (fun p => decide (InWide p)) = true := by
  decide +kernel


end LangtonsAnt
