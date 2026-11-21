import Phase49K1

namespace LangtonsAnt

theorem blank_entry_board :
    (run blank 12080).pos = (-56, -30) ∧ (run blank 12080).dir = .north ∧
      forall p, (run blank 12080).board p = decide (p ∈ blankAbsCells) := by
  have h := checkBlankJunk_true
  unfold checkBlankJunk at h
  cases hr : wideRun 12080 wideBlank with
  | none => simp [hr] at h
  | some t =>
    simp only [hr, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hpos, hdir⟩, hbox⟩, hbits⟩ := h
    have hs := wideRun_sound hr
    rw [wideBlank_toState] at hs
    have hbox' : forall p, p ∈ blankAbsCells -> InWide p := fun p hp =>
      of_decide_eq_true (List.all_eq_true.mp hbox p hp)
    refine ⟨?_, ?_, ?_⟩
    · rw [← hs]; exact hpos
    · rw [← hs]; exact hdir
    · intro p
      rw [← hs]
      change wideBoard t.bits p = _
      rw [hbits, wideBoard_wideCells _ hbox']

theorem seed_black_weight {p : Point} (hp : p ∈ highwaySeed.black) : weight p <= 0 := by
  have h : highwaySeed.black.all (fun p => decide (weight p <= 0)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

theorem blankEntryState_eq_perturb :
    blankEntryState = perturb junkMask highwaySeed.toState := by
  obtain ⟨hpos, hdir, hboard⟩ := blank_entry_board
  unfold blankEntryState
  generalize run blank 12080 = X at hpos hdir hboard ⊢
  have hext : forall s t : State, s.board = t.board -> s.pos = t.pos -> s.dir = t.dir -> s = t := by
    intro s t h1 h2 h3
    cases s; cases t
    simp only at h1 h2 h3
    subst h1; subst h2; subst h3
    rfl
  have hmem : forall p : Point, ((p.1 - 56, p.2 - 30) ∈ blankAbsCells) ↔
      (p ∈ highwaySeed.black ∨ p ∈ junk49) := by
    intro p
    unfold blankAbsCells
    rw [List.mem_map]
    constructor
    · rintro ⟨q, hq, he⟩
      have hqp : q = p := by
        simp only [Prod.mk.injEq] at he
        apply Prod.ext <;> omega
      subst hqp
      exact List.mem_append.mp hq
    · intro h
      exact ⟨p, List.mem_append.mpr h, rfl⟩
  apply hext
  · funext p
    simp only [normalize, rotateState, inverseRotation, rotatePoint, LangtonsAnt.translate,
      perturb, FiniteState.toState, junkMask, subPoint, negPoint]
    have he : (p.1 - -(-56 : Int), p.2 - -(-30 : Int)) = (p.1 - 56, p.2 - 30) := by
      apply Prod.ext <;> simp <;> omega
    rw [he, hboard]
    by_cases hs : p ∈ highwaySeed.black
    · have hj : p ∉ junk49 := fun hj => by
        have := junk49_weight hj; have := seed_black_weight hs; omega
      simp [hmem, hs, hj]
    · by_cases hj : p ∈ junk49 <;> simp [hmem, hs, hj]
  · simp only [normalize, rotateState, inverseRotation, rotatePoint, LangtonsAnt.translate,
      perturb, FiniteState.toState, hpos, negPoint, addPoint]
    decide
  · have h1 : forall Y : State, (normalize .north (-56, -30) Y).dir = rotateDir .north Y.dir :=
      fun _ => rfl
    have h2 : forall (m : Board) (Y : State), (perturb m Y).dir = Y.dir := fun _ _ => rfl
    have h3 : highwaySeed.toState.dir = .north := rfl
    rw [h1, h2, h3, hdir]
    rfl

/-! ## 2. The flipped blank state, the flipped seed state, and the strip reference -/

def phase49Time (k : Nat) : Nat := 104 * k + trailFlipTime

def flip49 (s : State) (k : Nat) : State :=
  flipCell (run s (phase49Time k)) (run s (phase49Time k)).pos

def ref49 (k : Nat) : State := LangtonsAnt.translate (offset (-2, -2) k) trailStart

theorem seed_run_weight (n : Nat) : weight (run highwaySeed.toState n).pos <= 0 :=
  highwaySeed_certificate.all_bounded n

theorem seed_run_junk (n : Nat) : junkMask (run highwaySeed.toState n).pos = false :=
  junkMask_of_weight (seed_run_weight n)

theorem flipCell_perturb (m : Board) (s : State) (p : Point) (hp : m p = false) :
    flipCell (perturb m s) p = perturb m (flipCell s p) := by
  have hb : flip (fun q => s.board q ^^ m q) p = fun q => flip s.board p q ^^ m q := by
    funext q
    by_cases h : q = p
    · subst q; simp [flip, hp]
    · simp [flip, h]
  simp only [flipCell, perturb, hb]

theorem flip49_blank (k : Nat) :
    flip49 blankEntryState k = perturb junkMask (flip49 highwaySeed.toState k) := by
  unfold flip49
  rw [blankEntryState_eq_perturb, run_perturb_avoids _ _ _ (fun j _ => seed_run_junk j)]
  have hp : forall (m : Board) (Y : State), (perturb m Y).pos = Y.pos := fun _ _ => rfl
  rw [hp, flipCell_perturb _ _ _ (seed_run_junk _)]

theorem seed_run_board_high {p : Point} (hp : 0 < weight p) (n : Nat) :
    (run highwaySeed.toState n).board p = false := by
  rw [board_unchanged_of_avoids highwaySeed.toState p n (by
    intro j _ he
    have := seed_run_weight j
    rw [he] at this
    omega)]
  change decide (p ∈ highwaySeed.black) = false
  exact decide_eq_false (fun hm => by have := seed_black_weight hm; omega)

theorem flipCell_board_ne {s : State} {p q : Point} (h : q ≠ p) :
    (flipCell s p).board q = s.board q := by
  simp [flipCell, flip, h]

/-- Region where the flipped seed state and the strip reference agree. -/
def region49 (k : Nat) (p : Point) : Prop :=
  weight p <= weight (offset (-2, -2) k) ∨ ¬TrailStrip p ∨ 0 < weight p

theorem flip49_seed_ref (k : Nat) :
    RegionAgree (region49 k) (flip49 highwaySeed.toState k) (ref49 k) := by
  let v := offset (-2, -2) k
  have hv : weight v <= 0 := offset_nonpos (by decide) k
  have ht := (seed_trail_agreement k).flip
  have hflip : flipCell (LangtonsAnt.translate v (run highwaySeed.toState trailFlipTime))
      (LangtonsAnt.translate v (run highwaySeed.toState trailFlipTime)).pos = ref49 k := by
    change flipCell (LangtonsAnt.translate v (run highwaySeed.toState trailFlipTime))
      (addPoint v (run highwaySeed.toState trailFlipTime).pos) = _
    rw [flipCell_translate, ref49, trailStart, flippedAt_toState]
  rw [hflip] at ht
  refine ⟨ht.pos, ht.dir, ?_⟩
  intro p hp
  rcases hp with hp | hp | hp
  · exact ht.board p (Or.inl hp)
  · exact ht.board p (Or.inr hp)
  · -- both boards are white above weight 0
    have hpos : p ≠ (run highwaySeed.toState (phase49Time k)).pos := by
      intro he; have := seed_run_weight (phase49Time k); rw [← he] at this; omega
    unfold flip49
    rw [flipCell_board_ne hpos, seed_run_board_high hp]
    have htb : forall (t : State) (q : Point), (LangtonsAnt.translate v t).board q =
        t.board (subPoint q v) := fun _ _ => rfl
    change false = (LangtonsAnt.translate v trailStart).board p
    rw [htb, trailStart, flippedAt_toState]
    have hw : 0 < weight (subPoint p v) := by
      simp only [weight, subPoint] at hp hv ⊢
      omega
    have hne : subPoint p v ≠ (run highwaySeed.toState trailFlipTime).pos := by
      intro he; have := seed_run_weight trailFlipTime; rw [← he] at this; omega
    rw [flipCell_board_ne hne, seed_run_board_high hw]

theorem ref49_region (k n : Nat) : region49 k (run (ref49 k) n).pos := by
  unfold ref49
  rw [translate_run]
  change region49 k (addPoint (offset (-2, -2) k) (run trailStart n).pos)
  rcases trail_all_safe n with hw | hs
  · left
    rw [weight_addPoint]
    omega
  · right; left
    unfold TrailStrip
    rw [trailCross_offset]
    exact hs

theorem flip49_seed_ref_run (k n : Nat) :
    RegionAgree (region49 k) (run (flip49 highwaySeed.toState k) n) (run (ref49 k) n) :=
  (flip49_seed_ref k).run n (fun j _ => ref49_region k j)

/-! ## 3. The strip reference never reads a junk cell before the aligned time -/

def junkBits : Nat := wideCells junk49

theorem junk49_inWide_check : junk49.all (fun p => decide (InWide p)) = true := by
  decide +kernel

theorem junkBits_board (p : Point) : wideBoard junkBits p = junkMask p := by
  unfold junkBits junkMask
  rw [wideBoard_wideCells junk49 (fun p hp =>
    of_decide_eq_true (List.all_eq_true.mp junk49_inWide_check p hp))]

/-! ### A precomputed shadow, so the per-step guard costs one bit lookup -/

/-- Box containing every prefix position (in original coordinates). -/
def ShadowBox (x : Point) : Prop := -72 <= x.1 ∧ x.1 < 58 ∧ -80 <= x.2 ∧ x.2 < 50

instance (x : Point) : Decidable (ShadowBox x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def shadowIdx (x : Point) : Nat := (x.1 + 72).toNat * 130 + (x.2 + 80).toNat

theorem shadowIdx_injective {x y : Point} (hx : ShadowBox x) (hy : ShadowBox y)
    (h : shadowIdx x = shadowIdx y) : x = y := by
  simp only [ShadowBox] at hx hy
  simp only [shadowIdx] at h
  apply Prod.ext <;> omega

/-- The junk cells moved up the diagonal by `k*(2,2)`, `k < 30`, inside the box. -/
def shadowCells : List Point :=
  (junk49.flatMap (fun j => (List.range 30).map (fun (k : Nat) => (j.1 + 2 * (k : Int), j.2 + 2 * (k : Int))))).filter
    (fun x => decide (ShadowBox x))

def orPow : Nat -> List Point -> Nat
  | acc, [] => acc
  | acc, x :: xs => orPow (acc ||| 2 ^ shadowIdx x) xs

theorem orPow_testBit (acc : Nat) (l : List Point) (x : Point) (hx : x ∈ l) :
    (orPow acc l).testBit (shadowIdx x) = true := by
  induction l generalizing acc with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [orPow]
    rcases List.mem_cons.mp hx with rfl | hm
    · -- the bit stays set once set
      have keep : forall (a : Nat) (l : List Point), a.testBit (shadowIdx x) = true ->
          (orPow a l).testBit (shadowIdx x) = true := by
        intro a l ha
        induction l generalizing a with
        | nil => exact ha
        | cons z zs ihz => exact ihz _ (by simp [Nat.testBit_or, ha])
      exact keep _ _ (by simp [Nat.testBit_or])
    · exact ih _ hm

def shadowBits : Nat := orPow 0 shadowCells

theorem junk49_x_check : junk49.all (fun j => decide (0 <= j.1)) = true := by
  decide +kernel

/-- Guard: weight at most 0, or in the box and not on the shadow. -/
def avoidJunk2 (x : Point) : Bool :=
  decide (weight x <= 0) || (decide (ShadowBox x) && !(shadowBits.testBit (shadowIdx x)))

theorem avoidJunk2_sound {x : Point} (h : avoidJunk2 x = true) (k : Nat) :
    junkMask (addPoint (offset (-2, -2) k) x) = false := by
  rw [southwest_offset]
  have he : addPoint (-2 * (k : Int), -2 * (k : Int)) x = (x.1 - 2 * k, x.2 - 2 * k) := by
    apply Prod.ext <;> simp [addPoint] <;> omega
  rw [he]
  simp only [avoidJunk2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  rcases h with hw | ⟨hb, hs⟩
  · apply junkMask_of_weight
    simp only [weight] at hw ⊢
    omega
  · unfold junkMask
    apply decide_eq_false
    intro hm
    have hx0 := of_decide_eq_true (List.all_eq_true.mp junk49_x_check _ hm)
    simp only [ShadowBox] at hb
    simp only at hx0
    have hk : k < 30 := by omega
    have hmem : x ∈ shadowCells := by
      unfold shadowCells
      rw [List.mem_filter]
      refine ⟨?_, decide_eq_true ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩⟩
      rw [List.mem_flatMap]
      refine ⟨_, hm, ?_⟩
      rw [List.mem_map]
      exact ⟨k, List.mem_range.mpr hk, by apply Prod.ext <;> simp <;> omega⟩
    have hbit := orPow_testBit 0 shadowCells x hmem
    unfold shadowBits at hs
    rw [hbit] at hs
    exact Bool.noConfusion hs

/-- No junk cell on the diagonal ray below `x` (the shifted copies `x + k*(-2,-2)`). -/
def avoidJunk (x : Point) : Bool :=
  (List.range ((weight x + 3).toNat / 4)).all (fun k => !(wideBoard junkBits (x.1 - 2 * k, x.2 - 2 * k)))

theorem avoidJunk_sound {x : Point} (h : avoidJunk x = true) (k : Nat) :
    junkMask (addPoint (offset (-2, -2) k) x) = false := by
  rw [southwest_offset]
  have he : addPoint (-2 * (k : Int), -2 * (k : Int)) x = (x.1 - 2 * k, x.2 - 2 * k) := by
    apply Prod.ext <;> simp [addPoint] <;> omega
  rw [he]
  by_cases hk : k < (weight x + 3).toNat / 4
  · have hh := List.all_eq_true.mp h k (List.mem_range.mpr hk)
    rw [junkBits_board] at hh
    simpa using hh
  · apply junkMask_of_weight
    simp only [weight] at hk ⊢
    omega


end LangtonsAnt
