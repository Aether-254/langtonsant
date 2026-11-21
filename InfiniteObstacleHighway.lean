import MultipleObstacles

namespace LangtonsAnt

/-- The one-sided infinite chain (-4-8*i, -4-8*i), expressed without an infinite search. -/
def infiniteChainMask (p : Point) : Bool :=
  decide (p.1 = p.2 ∧ p.1 <= -4 ∧ (p.1 + 4) % 8 = 0)

def infiniteChainTail : Board := fun p => infiniteChainMask (subPoint p chainShift)

theorem infiniteChainMask_iff (p : Point) :
    infiniteChainMask p = true ↔ exists i : Nat, p = chainPoint i := by
  simp only [infiniteChainMask, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨(-4 - p.1).toNat / 8, ?_⟩
    apply Prod.ext <;> simp only [chainPoint] <;> omega
  · rintro ⟨i, rfl⟩
    simp [chainPoint] <;> omega

theorem infiniteChainTail_weight {p : Point} (h : infiniteChainTail p = true) :
    weight p <= -24 := by
  obtain ⟨i, hi⟩ := (infiniteChainMask_iff (subPoint p chainShift)).mp h
  simp only [subPoint, chainShift, chainPoint, Prod.mk.injEq] at hi
  simp only [weight]
  omega

theorem infiniteChainMask_split (p : Point) :
    infiniteChainMask p = true ↔ p = chainHead ∨ infiniteChainTail p = true := by
  rw [infiniteChainMask_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | zero => exact Or.inl rfl
    | succ i =>
      right
      apply (infiniteChainMask_iff _).mpr
      refine ⟨i, ?_⟩
      apply Prod.ext <;> simp [chainPoint, subPoint, chainShift] <;> omega
  · intro h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨i, hi⟩ := (infiniteChainMask_iff _).mp h
      refine ⟨i + 1, ?_⟩
      apply Prod.ext <;> simp only [chainPoint, subPoint, chainShift, Prod.mk.injEq] at hi ⊢ <;> omega

theorem infiniteChain_decompose (s : State) :
    perturb infiniteChainMask s = perturb infiniteChainTail (flipCell s chainHead) := by
  have hb : (fun p => s.board p ^^ infiniteChainMask p) =
      fun p => flip s.board chainHead p ^^ infiniteChainTail p := by
    funext p
    by_cases hp : p = chainHead
    · subst p
      have hm : infiniteChainMask chainHead = true := by decide +kernel
      have ht : infiniteChainTail chainHead = false := by decide +kernel
      rw [hm, ht, flip_same, Bool.xor_false]
      cases s.board chainHead <;> rfl
    · have he : infiniteChainMask p = infiniteChainTail p := by
        have hi := infiniteChainMask_split p
        simp only [hp, false_or] at hi
        cases hm : infiniteChainMask p <;> cases ht : infiniteChainTail p <;> simp_all
      rw [flip_other _ hp, he]
  simp only [perturb, flipCell, hb]

def infiniteChainSeed : State := perturb infiniteChainMask highwaySeed.toState

theorem infiniteChain_prefix (n : Nat) (hn : n <= 548) :
    run infiniteChainSeed n = perturb infiniteChainTail (run chainCollisionSeed.toState n) := by
  unfold infiniteChainSeed
  rw [infiniteChain_decompose, ← chainCollisionSeed_toState]
  apply run_perturb_avoids
  intro j hj
  cases hc : infiniteChainTail (run chainCollisionSeed.toState j).pos
  · rfl
  · have hw := infiniteChainTail_weight hc
    have hb := (chainCollision_range j (by omega)).1
    omega

theorem infiniteChain_certificate : HighwayCertificate infiniteChainSeed 548 (-8, -8) 0 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro j hj
    rw [infiniteChain_prefix j (by omega)]
    exact (chainCollision_range j hj).2
  · have he := chainCollision_entry.perturb infiniteChainTail
    rw [← infiniteChain_prefix 548 (by omega)] at he
    change AgreesBelow (-16) (run infiniteChainSeed 548)
      (perturb (fun p => infiniteChainMask (subPoint p chainShift))
        (translate chainShift highwaySeed.toState)) at he
    rw [← perturb_translate] at he
    exact he

theorem infiniteChain_highway : HighwayFrom infiniteChainSeed 0 548 (-8, -8) :=
  infiniteChain_certificate.highway

theorem infiniteChain_reads (n : Nat) :
    readColor infiniteChainSeed n = readColor infiniteChainSeed (n % 548) :=
  infiniteChain_certificate.reads n

/-- No finite seed is added: the black cells are exactly the infinite continuation of the finite family. -/
def infiniteObstacles : State := perturb (fun p => infiniteChainMask (subPoint p chainOrigin)) blank

theorem infiniteObstacles_black (p : Point) : infiniteObstacles.board p = true ↔
    exists i : Nat, p = (-68 - 8 * (i : Int), -42 - 8 * (i : Int)) := by
  simp only [infiniteObstacles, perturb, blank, Bool.false_xor, infiniteChainMask_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Prod.ext <;> simp only [subPoint, chainOrigin, chainPoint, Prod.mk.injEq] at hi ⊢ <;> omega
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [hi]
    apply Prod.ext <;> simp [subPoint, chainOrigin, chainPoint] <;> omega

theorem infiniteObstacles_avoids_prefix (j : Nat) (hj : j < 12496) :
    infiniteChainMask (subPoint (run blank j).pos chainOrigin) = false := by
  cases hm : infiniteChainMask (subPoint (run blank j).pos chainOrigin)
  · rfl
  · obtain ⟨i, hi⟩ := (infiniteChainMask_iff _).mp hm
    have hmem : subPoint (run blank j).pos chainOrigin ∈ chainCells (i + 1) :=
      (chainCells_mem _ _).mpr ⟨i, by omega, hi⟩
    have hb := initialChain_avoids_prefix (i + 1) j hj
    simp only [initialChainMask, chainMask, hmem, decide_true] at hb
    exact hb

theorem infiniteObstacles_entry : AgreesBelow (-102) (run infiniteObstacles 12496)
    (translate chainOrigin infiniteChainSeed) := by
  have hp := run_perturb_avoids (fun p => infiniteChainMask (subPoint p chainOrigin))
    blank 12496 infiniteObstacles_avoids_prefix
  have hh := blank_chain_entry.perturb (fun p => infiniteChainMask (subPoint p chainOrigin))
  rw [← hp, ← perturb_translate] at hh
  exact hh

theorem infiniteObstacles_highway : HighwayFrom infiniteObstacles 12496 548 (-8, -8) := by
  have hc := infiniteChain_certificate.translate chainOrigin
  exact hc.highway_of_entry infiniteObstacles_entry

theorem infiniteObstacles_reads (n : Nat) :
    readColor infiniteObstacles (12496 + n) = readColor infiniteChainSeed (n % 548) := by
  have hc := infiniteChain_certificate.translate chainOrigin
  have he : AgreesBelow (0 + weight chainOrigin) (run infiniteObstacles 12496)
      (translate chainOrigin infiniteChainSeed) := infiniteObstacles_entry
  have hh := hc.reads_of_matches he n
  rw [translate_readColor] at hh
  simpa only [readColor, ← run_add] using hh

theorem infiniteObstacles_not_finite : ¬FiniteSupport infiniteObstacles.board := by
  rintro ⟨cells, hc⟩
  let i := (-(weightFloor cells)).toNat + 1
  let p : Point := (-68 - 8 * (i : Int), -42 - 8 * (i : Int))
  have hp : infiniteObstacles.board p = true := (infiniteObstacles_black p).mpr ⟨i, rfl⟩
  have hw := weightFloor_le (hc p hp)
  dsimp [p, i, weight] at hw
  omega

theorem HighwayFrom.advance_x {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) (n : Nat) (hn : T <= n) (k : Nat) :
    (run s (n + P * k)).pos.1 = (run s n).pos.1 + (k : Int) * v.1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, (h (n + P * k) (by omega)).1]
    simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    rw [ih]
    omega

theorem highway_horizontal_speeds_compatible {s : State} {T U P Q : Nat} {v w : Point}
    (hP : HighwayFrom s T P v) (hQ : HighwayFrom s U Q w) :
    (Q : Int) * v.1 = (P : Int) * w.1 := by
  have hp := hP.advance_x (T + U) (by omega) Q
  have hq := hQ.advance_x (T + U) (by omega) P
  rw [Nat.mul_comm Q P] at hq
  omega

/-- The 548-step drift is incompatible with every integer displacement at period 104. -/
theorem infiniteObstacles_no_period104 (T : Nat) (v : Point) :
    ¬HighwayFrom infiniteObstacles T 104 v := by
  intro h
  have he := highway_horizontal_speeds_compatible infiniteObstacles_highway h
  change 104 * (-8 : Int) = 548 * v.1 at he
  omega

theorem infiniteObstacles_not_eventuallyStandard : ¬EventuallyStandard infiniteObstacles := by
  rintro ⟨T, v, _, h⟩
  exact infiniteObstacles_no_period104 T v h.1

end LangtonsAnt
