import LangtonsAnt

namespace LangtonsAnt

def addPoint (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)
def subPoint (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)

@[simp] theorem addPoint_zero (p : Point) : addPoint p (0, 0) = p := by
  cases p
  simp [addPoint]

@[simp] theorem zero_addPoint (p : Point) : addPoint (0, 0) p = p := by
  cases p
  simp [addPoint]

theorem addPoint_assoc (p q r : Point) :
    addPoint (addPoint p q) r = addPoint p (addPoint q r) := by
  simp [addPoint, Int.add_assoc]

@[simp] theorem weight_addPoint (p q : Point) :
    weight (addPoint p q) = weight p + weight q := by
  simp [weight, addPoint]
  omega

@[simp] theorem subPoint_addPoint (p q : Point) :
    subPoint (addPoint p q) p = q := by
  apply Prod.ext <;> simp [addPoint, subPoint] <;> omega

@[simp] theorem addPoint_subPoint (p q : Point) :
    addPoint p (subPoint q p) = q := by
  apply Prod.ext <;> simp [addPoint, subPoint] <;> omega

def translate (v : Point) (s : State) : State :=
  { board := fun p => s.board (subPoint p v), pos := addPoint v s.pos, dir := s.dir }

@[simp] theorem translate_zero (s : State) : translate (0, 0) s = s := by
  cases s
  simp [translate, subPoint]

theorem translate_add (v w : Point) (s : State) :
    translate v (translate w s) = translate (addPoint v w) s := by
  have hp : forall p, subPoint (subPoint p v) w = subPoint p (addPoint v w) := by
    intro p
    apply Prod.ext <;> simp [subPoint, addPoint] <;> omega
  simp only [translate, hp, addPoint_assoc]

theorem move_addPoint (v p : Point) (d : Direction) :
    move (addPoint v p) d = addPoint v (move p d) := by
  cases d <;> apply Prod.ext <;> simp [move, addPoint] <;> omega

theorem translate_step (v : Point) (s : State) :
    step (translate v s) = translate v (step s) := by
  have hflip : flip (fun p => s.board (subPoint p v)) (addPoint v s.pos) =
      fun p => flip s.board s.pos (subPoint p v) := by
    funext p
    have heq : p = addPoint v s.pos ↔ subPoint p v = s.pos := by
      constructor
      · intro h
        simp [h]
      · intro h
        rw [← h, addPoint_subPoint]
    simp [flip, heq]
  simp [step, translate, hflip, move_addPoint]

theorem translate_run (v : Point) (s : State) (n : Nat) :
    run (translate v s) n = translate v (run s n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run_succ, ih, translate_step]

theorem translate_readColor (v : Point) (s : State) (n : Nat) :
    readColor (translate v s) n = readColor s n := by
  unfold readColor
  rw [translate_run]
  simp only [translate, subPoint_addPoint]

/-- Only cells in this half-plane may influence the certified future. -/
structure AgreesBelow (cut : Int) (s t : State) : Prop where
  pos : s.pos = t.pos
  dir : s.dir = t.dir
  board : forall p, weight p <= cut -> s.board p = t.board p

theorem AgreesBelow.refl (cut : Int) (s : State) : AgreesBelow cut s s :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem AgreesBelow.trans {cut : Int} {s t u : State}
    (h : AgreesBelow cut s t) (g : AgreesBelow cut t u) : AgreesBelow cut s u :=
  ⟨h.pos.trans g.pos, h.dir.trans g.dir, fun p hp => (h.board p hp).trans (g.board p hp)⟩

theorem AgreesBelow.weaken {a b : Int} {s t : State}
    (h : AgreesBelow a s t) (hab : b <= a) : AgreesBelow b s t :=
  ⟨h.pos, h.dir, fun p hp => h.board p (by omega)⟩

theorem AgreesBelow.step {cut : Int} {s t : State}
    (h : AgreesBelow cut s t) (hp : weight t.pos <= cut) :
    AgreesBelow cut (LangtonsAnt.step s) (LangtonsAnt.step t) := by
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

theorem AgreesBelow.run {cut : Int} {s t : State} (h : AgreesBelow cut s t)
    (n : Nat) (hb : forall j, j < n -> weight (LangtonsAnt.run t j).pos <= cut) :
    AgreesBelow cut (LangtonsAnt.run s n) (LangtonsAnt.run t n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact (ih (fun j hj => hb j (by omega))).step (hb n (by omega))

theorem AgreesBelow.translate {cut : Int} {s t : State}
    (h : AgreesBelow cut s t) (v : Point) :
    AgreesBelow (cut + weight v) (LangtonsAnt.translate v s) (LangtonsAnt.translate v t) := by
  refine ⟨congrArg (addPoint v) h.pos, h.dir, ?_⟩
  intro p hp
  apply h.board
  simp only [weight, subPoint] at hp ⊢
  omega

/-- A finite-time restart plus a half-plane guard, not an infinite-trace assumption. -/
structure HighwayCertificate (s : State) (period : Nat) (drift : Point) (cut : Int) : Prop where
  positive : 0 < period
  outward : weight drift <= 0
  bounded : forall j, j < period -> weight (run s j).pos <= cut
  restart : AgreesBelow (cut + weight drift) (run s period) (translate drift s)

def offset (v : Point) : Nat -> Point
  | 0 => (0, 0)
  | k + 1 => addPoint (offset v k) v

theorem offset_nonpos {v : Point} (hv : weight v <= 0) (k : Nat) :
    weight (offset v k) <= 0 := by
  induction k with
  | zero => simp [offset, weight]
  | succ k ih => rw [offset, weight_addPoint]; omega

theorem HighwayCertificate.blocks {s : State} {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate s P v cut) (k : Nat) :
    AgreesBelow (cut + weight (offset v k)) (run s (P * k)) (translate (offset v k) s) := by
  induction k with
  | zero => simpa [offset, weight] using AgreesBelow.refl cut s
  | succ k ih =>
    have hrun := ih.run P (by
      intro j hj
      rw [translate_run]
      change weight (addPoint (offset v k) (run s j).pos) <= _
      rw [weight_addPoint]
      have := c.bounded j hj
      omega)
    have hnext := c.restart.translate (offset v k)
    rw [← translate_run, translate_add] at hnext
    have hweak := hrun.weaken
      (show cut + weight v + weight (offset v k) <= cut + weight (offset v k) by
        have := c.outward
        omega)
    have h := hweak.trans hnext
    rw [← run_add] at h
    simpa only [Nat.mul_succ, offset, weight_addPoint, Int.add_assoc,
      Int.add_left_comm, Int.add_comm] using h

theorem HighwayCertificate.block_prefix {s : State} {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate s P v cut) (k j : Nat) (hj : j <= P) :
    AgreesBelow (cut + weight (offset v k))
      (run s (P * k + j)) (translate (offset v k) (run s j)) := by
  rw [run_add, ← translate_run]
  apply (c.blocks k).run
  intro i hi
  rw [translate_run]
  change weight (addPoint (offset v k) (run s i).pos) <= _
  rw [weight_addPoint]
  have := c.bounded i (by omega)
  omega

theorem HighwayCertificate.highway {s : State} {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate s P v cut) : HighwayFrom s 0 P v := by
  intro n _
  let k := n / P
  let j := n % P
  have hj : j < P := Nat.mod_lt n c.positive
  have hn : n = P * k + j := by
    dsimp [k, j]
    exact (Nat.div_add_mod n P).symm
  have hnP : n + P = P * (k + 1) + j := by rw [Nat.mul_succ]; omega
  have h0 := c.block_prefix k j (by omega)
  have h1 := c.block_prefix (k + 1) j (by omega)
  rw [hnP, hn]
  constructor
  · rw [h0.pos, h1.pos]
    change addPoint (offset v (k + 1)) (run s j).pos =
      addPoint (addPoint (offset v k) (run s j).pos) v
    change addPoint (addPoint (offset v k) v) (run s j).pos = _
    apply Prod.ext <;> simp [addPoint] <;> omega
  · exact h1.dir.trans h0.dir.symm

theorem HighwayCertificate.all_bounded {s : State} {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate s P v cut) (n : Nat) : weight (run s n).pos <= cut := by
  have hj := Nat.mod_lt n c.positive
  have hn : n = P * (n / P) + n % P := (Nat.div_add_mod n P).symm
  have h := c.block_prefix (n / P) (n % P) (by omega)
  rw [hn, h.pos]
  change weight (addPoint (offset v (n / P)) (run s (n % P)).pos) <= cut
  rw [weight_addPoint]
  have := c.bounded (n % P) hj
  have := offset_nonpos c.outward (n / P)
  omega

theorem HighwayCertificate.reads {s : State} {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate s P v cut) (n : Nat) :
    readColor s n = readColor s (n % P) := by
  have hj := Nat.mod_lt n c.positive
  have hn : n = P * (n / P) + n % P := (Nat.div_add_mod n P).symm
  have h := c.block_prefix (n / P) (n % P) (by omega)
  unfold readColor
  rw [hn, h.pos]
  rw [h.board]
  · simp [translate]
  · change weight (addPoint (offset v (n / P)) (run s (n % P)).pos) <= _
    rw [weight_addPoint]
    have := c.bounded (n % P) hj
    omega

theorem HighwayCertificate.matches_forever {seed s : State} {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate seed P v cut) (h : AgreesBelow cut s seed) (n : Nat) :
    AgreesBelow cut (run s n) (run seed n) :=
  h.run n (fun j _ => c.all_bounded j)

/-- Arbitrary cells outside the protected half-plane do not affect the infinite highway. -/
theorem HighwayCertificate.highway_of_matches {seed s : State}
    {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate seed P v cut) (h : AgreesBelow cut s seed) :
    HighwayFrom s 0 P v := by
  intro n hn
  have h0 := c.matches_forever h n
  have h1 := c.matches_forever h (n + P)
  have hc := c.highway n hn
  simpa only [h0.pos, h0.dir, h1.pos, h1.dir] using hc

theorem HighwayCertificate.reads_of_matches {seed s : State}
    {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate seed P v cut) (h : AgreesBelow cut s seed) (n : Nat) :
    readColor s n = readColor seed (n % P) := by
  have hm := c.matches_forever h n
  have hr : readColor s n = readColor seed n := by
    unfold readColor
    rw [hm.pos]
    exact hm.board _ (c.all_bounded n)
  exact hr.trans (c.reads n)

theorem HighwayCertificate.translate {s : State} {P : Nat} {v : Point} {cut : Int}
    (c : HighwayCertificate s P v cut) (w : Point) :
    HighwayCertificate (LangtonsAnt.translate w s) P v (cut + weight w) := by
  refine ⟨c.positive, c.outward, ?_, ?_⟩
  · intro j hj
    rw [translate_run]
    change weight (addPoint w (run s j).pos) <= _
    rw [weight_addPoint]
    have := c.bounded j hj
    omega
  · have h := c.restart.translate w
    have hcomm : LangtonsAnt.translate w (LangtonsAnt.translate v s) =
        LangtonsAnt.translate v (LangtonsAnt.translate w s) := by
      rw [translate_add, translate_add]
      congr 1
      apply Prod.ext <;> simp [addPoint, Int.add_comm]
    rw [hcomm, ← translate_run] at h
    simpa only [Int.add_assoc, Int.add_left_comm, Int.add_comm] using h

theorem highwayFrom_run {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom (run s T) 0 P v) : HighwayFrom s T P v := by
  intro n hn
  have hh := h (n - T) (by omega)
  simp only [← run_add] at hh
  have h0 : T + (n - T) = n := by omega
  have h1 : T + (n - T + P) = n + P := by omega
  simpa only [h0, h1] using hh

theorem HighwayCertificate.highway_of_entry {seed s : State} {T P : Nat}
    {v : Point} {cut : Int}
    (c : HighwayCertificate seed P v cut) (h : AgreesBelow cut (run s T) seed) :
    HighwayFrom s T P v :=
  highwayFrom_run (c.highway_of_matches h)

end LangtonsAnt
