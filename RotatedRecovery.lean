import RecoveryCertificate
import FreshPhases

/-!
# Recovery certificates whose new highway turns by a quarter

After some mature flips the ant re-enters a standard highway heading east or west, i.e.
drifting northwest or southeast.  Such a highway runs parallel to the original front line
`x+y = const`, so the weight of its positions is periodic.  The certificate checks:

* the finite prefix stays in `x+y <= 0` (packed run of the flipped seed state);
* the flipped state, rotated back into the standard frame, reaches a translated seed entry
  (packed run of the rotated state);
* one period of the rotated seed path stays in `x+y <= 0`; together with the drift having
  weight zero this bounds the entire infinite tail.

Hence the recovery only ever reads cells with `x+y <= 0` and transfers to every history.
-/

namespace LangtonsAnt

def rotFlipped (f : Nat) (r : Direction) : FiniteState :=
  (flippedAt f).rotate (inverseRotation r)

theorem rotFlipped_toState (f : Nat) (r : Direction) :
    (rotFlipped f r).toState = rotateState (inverseRotation r) (flippedAt f).toState :=
  FiniteState.toState_rotate _ _

structure RotatedRecoveryCertificate (f d : Nat) (r : Direction) (origin : Point) : Prop where
  turn : r = .east ∨ r = .west
  bounded : forall j, j < d -> weight (run (flippedAt f).toState j).pos <= 0
  entry : AgreesBelow (weight (rotatePoint (inverseRotation r) origin))
    (run (rotFlipped f r).toState d)
    (translate (rotatePoint (inverseRotation r) origin) highwaySeed.toState)
  tail : forall j, j < 104 -> weight (addPoint origin (rotatePoint r (cyclePos j))) <= 0

def checkRotatedRecovery (f d : Nat) (r : Direction) (origin : Point) : Bool :=
  let F := flippedAt f
  let G := rotFlipped f r
  let o := rotatePoint (inverseRotation r) origin
  (r == .east || r == .west) &&
    F.black.all (fun p => decide (InBox p)) && checkPackedBounded 0 d F.toPacked &&
    G.black.all (fun p => decide (InBox p)) &&
    checkPackedEntry d G.toPacked (weight o) (highwaySeed.translate o) &&
    (List.range 104).all (fun j => decide (weight (addPoint origin (rotatePoint r (cyclePos j))) <= 0))

theorem checkRotatedRecovery_sound {f d : Nat} {r : Direction} {origin : Point}
    (h : checkRotatedRecovery f d r origin = true) :
    RotatedRecoveryCertificate f d r origin := by
  simp only [checkRotatedRecovery, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hr, hF⟩, hb⟩, hG⟩, he⟩, ht⟩ := h
  have hFbox : forall p, p ∈ (flippedAt f).black -> InBox p := by
    intro p hp
    exact of_decide_eq_true (List.all_eq_true.mp hF p hp)
  have hGbox : forall p, p ∈ (rotFlipped f r).black -> InBox p := by
    intro p hp
    exact of_decide_eq_true (List.all_eq_true.mp hG p hp)
  have hFe := (flippedAt f).toPacked_toState hFbox
  have hGe := (rotFlipped f r).toPacked_toState hGbox
  refine ⟨hr, ?_, ?_, ?_⟩
  · simpa only [hFe] using checkPackedBounded_sound hb
  · simpa only [hGe, FiniteState.toState_translate] using checkPackedEntry_sound he
  · intro j hj
    exact of_decide_eq_true (List.all_eq_true.mp ht j (List.mem_range.mpr hj))

/-- A quarter turn to east or west keeps weight differences along the diagonal. -/
theorem weight_rotate_shift {r : Direction} (hr : r = .east ∨ r = .west) (c : Point) (q : Int) :
    weight (rotatePoint r (c.1 - 2 * q, c.2 - 2 * q)) = weight (rotatePoint r c) := by
  rcases hr with rfl | rfl <;> simp only [rotatePoint, weight] <;> omega

theorem RotatedRecoveryCertificate.standard {f d : Nat} {r : Direction} {o : Point}
    (c : RotatedRecoveryCertificate f d r o) :
    StandardHighwayFrom (flippedAt f).toState d (rotatePoint r (-2, -2)) := by
  have hG := standard_highway_of_entry _ c.entry
  have hR := hG.rotate r
  rw [rotFlipped_toState, inverse_rotateState] at hR
  exact hR

theorem RotatedRecoveryCertificate.all_bounded {f d : Nat} {r : Direction} {o : Point}
    (c : RotatedRecoveryCertificate f d r o) (n : Nat) :
    weight (run (flippedAt f).toState n).pos <= 0 := by
  by_cases hn : n < d
  · exact c.bounded n hn
  · let o' := rotatePoint (inverseRotation r) o
    have hc := highwaySeed_certificate.translate o'
    have he : AgreesBelow (0 + weight o') (run (rotFlipped f r).toState d)
        (translate o' highwaySeed.toState) := by simpa only [Int.zero_add] using c.entry
    have hm := hc.matches_forever he (n - d)
    rw [← run_add, translate_run] at hm
    have heq : d + (n - d) = n := by omega
    rw [heq] at hm
    -- position of the rotated state at time n
    have hpos : (run (rotFlipped f r).toState n).pos =
        addPoint o' (run highwaySeed.toState (n - d)).pos := hm.pos
    -- rotate back to the original frame
    have hback : (run (flippedAt f).toState n).pos =
        rotatePoint r (run (rotFlipped f r).toState n).pos := by
      rw [rotFlipped_toState, rotate_run]
      change _ = rotatePoint r (rotatePoint (inverseRotation r) (run (flippedAt f).toState n).pos)
      simp
    obtain ⟨q, j, hj, hqj⟩ : exists q j, j < 104 ∧ n - d = 104 * q + j :=
      ⟨(n - d) / 104, (n - d) % 104, Nat.mod_lt _ (by decide), (Nat.div_add_mod _ 104).symm⟩
    rw [hback, hpos, hqj, seed_pos_decomp q j hj, rotatePoint_add, weight_addPoint,
      weight_rotate_shift c.turn]
    have ho : rotatePoint r o' = o := by simp [o']
    rw [ho]
    have ht := c.tail j hj
    rw [weight_addPoint] at ht
    exact ht

theorem RotatedRecoveryCertificate.translated {f d : Nat} {r : Direction} {o : Point}
    (c : RotatedRecoveryCertificate f d r o) {s : State} (v : Point)
    (h : AgreesBelow (weight v) s (translate v (run highwaySeed.toState f))) :
    StandardHighwayFrom (flipCell s s.pos) d (rotatePoint r (-2, -2)) := by
  apply (c.standard.translate v).of_agreesBelow
  · rw [flippedAt_toState, ← flipCell_translate, h.pos]
    change AgreesBelow (weight v)
      (flipCell s (addPoint v (run highwaySeed.toState f).pos))
      (flipCell (translate v (run highwaySeed.toState f)) (addPoint v (run highwaySeed.toState f).pos))
    rw [flipCell_eq_perturb, flipCell_eq_perturb]
    exact h.perturb _
  · intro n
    rw [translate_run]
    change weight (addPoint v (run (flippedAt f).toState n).pos) <= _
    rw [weight_addPoint]
    have hb := c.all_bounded n
    omega

theorem RotatedRecoveryCertificate.after_blocks {f d : Nat} {r : Direction} {o : Point}
    (c : RotatedRecoveryCertificate f d r o) {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    StandardHighwayFrom (flipCell (run s (104 * k + f)) (run s (104 * k + f)).pos) d
      (rotatePoint r (-2, -2)) := by
  let v := offset (-2, -2) k
  have hm := highwaySeed_certificate.matches_forever h (104 * k)
  have hp := highwaySeed_certificate.blocks k
  have hv : weight v <= 0 := offset_nonpos (by decide) k
  have he : AgreesBelow (weight v) (run s (104 * k)) (translate v highwaySeed.toState) :=
    (hm.weaken hv).trans (by simpa only [Int.zero_add] using hp)
  have hg := he.run f (by
    intro j _
    rw [translate_run]
    change weight (addPoint v (run highwaySeed.toState j).pos) <= _
    rw [weight_addPoint]
    have hb := highwaySeed_certificate.all_bounded j
    omega)
  rw [← run_add, translate_run] at hg
  exact c.translated v hg

/-- Every rotated certificate yields eventual standardness after any history. -/
theorem RotatedRecoveryCertificate.eventually {f d : Nat} {r : Direction} {o : Point}
    (c : RotatedRecoveryCertificate f d r o) {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    EventuallyStandard (flipCell (run s (104 * k + f)) (run s (104 * k + f)).pos) :=
  ⟨d, rotatePoint r (-2, -2), diagonal_rotated_southwest r, c.after_blocks h k⟩

end LangtonsAnt
