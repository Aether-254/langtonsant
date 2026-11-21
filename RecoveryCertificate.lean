import HighwayRecovery
import PackedFinite

namespace LangtonsAnt

def flippedAt (n : Nat) : FiniteState :=
  let s := highwaySeed.run n
  { s with black := toggleCells s.black s.pos }

theorem flippedAt_toState (n : Nat) : (flippedAt n).toState =
    flipCell (run highwaySeed.toState n) (run highwaySeed.toState n).pos := by
  have h := (highwaySeed.run n).toState_flip (highwaySeed.run n).pos
  change (flippedAt n).toState = flipCell (highwaySeed.run n).toState
    (highwaySeed.run n).toState.pos at h
  simpa only [FiniteState.toState_run] using h

/-- A finite recovery prefix staying inside the original highway's protected half-plane. -/
structure RecoveryCertificate (flipTime delay : Nat) (origin : Point) : Prop where
  outward : weight origin <= 0
  bounded : forall j, j < delay -> weight (run (flippedAt flipTime).toState j).pos <= 0
  entry : AgreesBelow (weight origin) (run (flippedAt flipTime).toState delay)
    (translate origin highwaySeed.toState)

def checkRecovery (flipTime delay : Nat) (origin : Point) : Bool :=
  let f := flippedAt flipTime
  decide (weight origin <= 0) && f.black.all (fun p => decide (InBox p)) &&
    checkPackedBounded 0 delay f.toPacked &&
    checkPackedEntry delay f.toPacked (weight origin) (highwaySeed.translate origin)

theorem checkRecovery_sound {flipTime delay : Nat} {origin : Point}
    (h : checkRecovery flipTime delay origin = true) : RecoveryCertificate flipTime delay origin := by
  simp only [checkRecovery, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb : forall p, p ∈ (flippedAt flipTime).black -> InBox p := by
    intro p hp
    exact of_decide_eq_true (List.all_eq_true.mp h.1.1.2 p hp)
  have he := (flippedAt flipTime).toPacked_toState hb
  refine ⟨h.1.1.1, ?_, ?_⟩
  · simpa only [he] using checkPackedBounded_sound h.1.2
  · simpa only [he, FiniteState.toState_translate] using checkPackedEntry_sound h.2

theorem RecoveryCertificate.standard {f d : Nat} {p : Point}
    (c : RecoveryCertificate f d p) : StandardHighwayFrom (flippedAt f).toState d (-2, -2) :=
  standard_highway_of_entry p c.entry

theorem RecoveryCertificate.all_bounded {f d : Nat} {p : Point}
    (c : RecoveryCertificate f d p) (n : Nat) : weight (run (flippedAt f).toState n).pos <= 0 := by
  by_cases hn : n < d
  · exact c.bounded n hn
  · have hc := highwaySeed_certificate.translate p
    have he : AgreesBelow (0 + weight p) (run (flippedAt f).toState d)
        (translate p highwaySeed.toState) := by simpa only [Int.zero_add] using c.entry
    have hm := hc.matches_forever he (n - d)
    have hb := hc.all_bounded (n - d)
    rw [← hm.pos, ← run_add] at hb
    have heq : d + (n - d) = n := by omega
    rw [heq] at hb
    have ho := c.outward
    omega

theorem RecoveryCertificate.translated {f d : Nat} {p : Point}
    (c : RecoveryCertificate f d p) {s : State} (v : Point)
    (h : AgreesBelow (weight v) s (translate v (run highwaySeed.toState f))) :
    StandardHighwayFrom (flipCell s s.pos) d (-2, -2) := by
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

theorem RecoveryCertificate.after_blocks {f d : Nat} {p : Point}
    (c : RecoveryCertificate f d p) {s : State}
    (h : AgreesBelow 0 s highwaySeed.toState) (k : Nat) :
    StandardHighwayFrom (flipCell (run s (104 * k + f)) (run s (104 * k + f)).pos) d (-2, -2) := by
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

theorem RecoveryCertificate.after_entry {f d : Nat} {p : Point}
    (c : RecoveryCertificate f d p) {s : State} {T : Nat} {r : Direction} {origin : Point}
    (h : EntryAt s T r origin) (k : Nat) :
    StandardHighwayFrom
      (flipCell (run s (T + (104 * k + f))) (run s (T + (104 * k + f))).pos)
      d (rotatePoint r (-2, -2)) := by
  have hh := c.after_blocks h k
  have hp := (hh.rotate r).translate origin
  change StandardHighwayFrom
    (pose r origin (flipCell (run (normalize r origin (run s T)) (104 * k + f))
      (run (normalize r origin (run s T)) (104 * k + f)).pos)) d _ at hp
  rw [← flipCell_pose, ← pose_run, pose_normalize, ← run_add] at hp
  exact hp

end LangtonsAnt
