import PersistA.SharedBoundary

/-!
Cyclic rebasing at the rank-zero gates. The gates face south in the original
coordinates. Normalizing that heading to north rotates the displacement
(2,-2) to (-2,2), and each gate block has displacement (-1,1).
-/

namespace LangtonsAnt.PersistA.GateRebase

open FirstVisitCycle TwoGateDecomposition SharedBoundary

/-- Repeat the finite prefix, then start it at the specified phase. -/
def cyclicShift (P : Nat) (w : Nat -> Bool) (start : Nat) : Nat -> Bool :=
  fun n => w ((start + n) % P)

theorem cyclicShift_consistent {P : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hP : 0 < P) (start : Nat) :
    ConsistentWord P (cyclicShift P w start) := by
  have hh := hw.realization_highway hP
  have ht : HighwayFrom (wordRealization P w) start P (wordDrift P w) :=
    fun n _ => hh n (by omega)
  have hc := periodic_tail_consistent_at_start (wordRealization_finite P w) hP ht
  apply hc.congr
  intro i _
  exact hw.realization_reads hP (start + i)

theorem trace_shift (w : Nat -> Bool) (start n : Nat) :
    wordTrace w (start + n) =
      (addPoint (wordPos w start)
        (rotatePoint (wordTrace w start).2 (wordPos (fun i => w (start + i)) n)),
       rotateDir (wordTrace w start).2 (wordTrace (fun i => w (start + i)) n).2) := by
  induction n with
  | zero => simp [wordTrace, wordPos]
  | succ n ih =>
    rw [show start + (n + 1) = (start + n) + 1 by omega, wordTrace, ih]
    simp only [wordTrace, wordPos, rotatePoint_move,
      rotateDir_turn, move_addPoint]

theorem cyclicShift_pos {P start : Nat} {w : Nat -> Bool} (hs : start < P) (n : Nat) :
    wordPos (cyclicShift P w start) n =
      rotatePoint (inverseRotation (wordTrace w start).2)
        (subPoint (wordPos (repeatWord P w) (start + n)) (wordPos w start)) := by
  have ht := congrArg Prod.fst (trace_shift (repeatWord P w) start n)
  have he := repeatWord_trace w (Nat.le_of_lt hs)
  change wordPos (repeatWord P w) (start + n) =
    addPoint (wordPos (repeatWord P w) start)
      (rotatePoint (wordTrace (repeatWord P w) start).2
        (wordPos (cyclicShift P w start) n)) at ht
  have hp : wordPos (repeatWord P w) start = wordPos w start := congrArg Prod.fst he
  rw [hp, he] at ht
  rw [ht]
  have hsub (a b : Point) : subPoint (addPoint a b) a = b := by
    apply Prod.ext <;> simp only [subPoint, addPoint] <;> omega
  rw [hsub, rotatePoint_inverse]

theorem cyclicShift_drift {P start : Nat} {w : Nat -> Bool}
    (hh : (wordTrace w P).2 = .north) (hs : start < P) :
    wordDrift P (cyclicShift P w start) =
      rotatePoint (inverseRotation (wordTrace w start).2) (wordDrift P w) := by
  rw [wordDrift, cyclicShift_pos hs]
  have hp := congrArg Prod.fst (repeatWord_trace_period hh start)
  change wordPos (repeatWord P w) (start + P) =
    addPoint (wordDrift P w) (wordPos (repeatWord P w) start) at hp
  rw [hp, show wordPos (repeatWord P w) start = wordPos w start from
    congrArg Prod.fst (repeatWord_trace w (Nat.le_of_lt hs))]
  congr 1
  apply Prod.ext <;> simp [subPoint, addPoint]

/-- The closed-run lengths for a specified core, rather than an existentially
chosen core. Both paths include the endpoint immediately before the E,S bridge. -/
theorem core_lengths {P : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2,-2)) (c : Core P w) :
    exists d0 d1 : Nat, 0 < d0 /\ 0 < d1 /\ P = d0 + d1 + 4 /\
      let hP : 0 < P := Nat.zero_lt_of_lt c.a0_lt
      let p0 := ContinuousPhasePath.ofStart hP c.a0 d0
      let p1 := ContinuousPhasePath.ofStart hP c.a1 d1
      p0.phase d0 = Drift.pred P c.b0 /\ p0.pos w d0 = p0.pos w 0 /\
      p1.phase d1 = Drift.pred P c.b1 /\ p1.pos w d1 = p1.pos w 0 := by
  have hv : Not (((2 : Int),(-2 : Int)) = (0,0)) := by decide
  have e := core_exit_data hw hd c
  have total := core_total_gap hw hd c
  let D0 := Drift.stableTime (2,-2) P w (Drift.pred P c.b0) -
    Drift.stableTime (2,-2) P w c.a0
  let D1 := Drift.stableTime (2,-2) P w (Drift.pred P c.b1) -
    Drift.stableTime (2,-2) P w c.a1
  have hd0 : 0 < D0 := Int.sub_pos.mpr e.2.2.2.2.1
  have hd1 : 0 < D1 := Int.sub_pos.mpr e.2.2.2.2.2
  have htotal : (P : Int) = 4 + D0 + D1 := total
  have n0 : (D0.toNat : Int) = D0 := Int.toNat_of_nonneg (by omega)
  have n1 : (D1.toNat : Int) = D1 := Int.toNat_of_nonneg (by omega)
  have p0 := GatePath.stable_gap_is_actual_closed_path hd hv c.a0_lt
    (UnitDiagonalMatching.pred_lt c.b0_lt) e.1 (len := D0.toNat)
    (by rw [n0]; dsimp [D0, Drift.pred]; omega)
  have p1 := GatePath.stable_gap_is_actual_closed_path hd hv c.a1_lt
    (UnitDiagonalMatching.pred_lt c.b1_lt) e.2.1 (len := D1.toNat)
    (by rw [n1]; dsimp [D1, Drift.pred]; omega)
  exact ⟨D0.toNat, D1.toNat, by omega, by omega, by omega,
    p0.2.1, p0.2.2, p1.2.1, p1.2.2⟩

private theorem phase_succ (P start n : Nat) :
    (start + (n + 1)) % P = Drift.succ P ((start + n) % P) := by
  simp only [Drift.succ, UnitDiagonalMatching.succ]
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem repeat_pos_step {P : Nat} {w : Nat -> Bool} (hP : 0 < P)
    (hh : (wordTrace w P).2 = .north) (start n : Nat) :
    wordPos (repeatWord P w) (start + (n + 1)) =
      move (wordPos (repeatWord P w) (start + n))
        (Drift.outDir w ((start + n) % P)) := by
  have he := (ContinuousPhasePath.ofStart hP start (n + 1)).pos_step
    (w := w) (r := n) (by omega)
  rw [ContinuousPhasePath.pos_ofStart hP hh,
    ContinuousPhasePath.pos_ofStart hP hh] at he
  exact he

theorem bridge_end {P start b target len : Nat} {w : Nat -> Bool}
    (hP : 0 < P) (hh : (wordTrace w P).2 = .north) (hb : b < P)
    (hphase : (start + len) % P = Drift.pred P b)
    (hreturn : wordPos (repeatWord P w) (start + len) =
      wordPos (repeatWord P w) start)
    (he : Drift.outDir w (Drift.pred P b) = .east)
    (hs : Drift.outDir w b = .south) (ht : Drift.succ P b = target) :
    (start + (len + 2)) % P = target /\
      wordPos (repeatWord P w) (start + (len + 2)) =
        addPoint (wordPos (repeatWord P w) start) (1,-1) := by
  have h1 : (start + (len + 1)) % P = b := by
    rw [phase_succ, hphase]
    exact UnitDiagonalMatching.succ_pred hb
  constructor
  · rw [show len + 2 = (len + 1) + 1 by omega, phase_succ, h1, ht]
  · rw [show len + 2 = (len + 1) + 1 by omega,
      repeat_pos_step hP hh, h1, hs, repeat_pos_step hP hh, hphase, he, hreturn]
    rfl

/-- Exact chronological gate blocks, including the two bridge steps after each
closed run. All positions use the canonical north-heading rebased word. -/
structure GateBlocks (P : Nat) (w : Nat -> Bool) (c : Core P w) (d0 d1 : Nat) : Prop where
  positive0 : 0 < d0
  positive1 : 0 < d1
  period_eq : P = d0 + d1 + 4
  exit0 : (c.a0 + d0) % P = Drift.pred P c.b0
  bridge0 : (c.a0 + (d0 + 1)) % P = c.b0
  cut_phase : (c.a0 + (d0 + 2)) % P = c.a1
  exit1 : (c.a0 + (d0 + 2 + d1)) % P = Drift.pred P c.b1
  bridge1 : (c.a0 + (d0 + 2 + d1 + 1)) % P = c.b1
  return0 : wordPos (cyclicShift P w c.a0) d0 = (0,0)
  east0 : wordPos (cyclicShift P w c.a0) (d0 + 1) = (-1,0)
  cut_pos : wordPos (cyclicShift P w c.a0) (d0 + 2) = (-1,1)
  cut_heading : (wordTrace (cyclicShift P w c.a0) (d0 + 2)).2 = .north
  return1 : wordPos (cyclicShift P w c.a0) (d0 + 2 + d1) = (-1,1)
  east1 : wordPos (cyclicShift P w c.a0) (d0 + 2 + d1 + 1) = (-2,1)
  drift : wordDrift P (cyclicShift P w c.a0) = (-2,2)

private theorem shift_add (P start cut n : Nat) (w : Nat -> Bool) :
    cyclicShift P w start (cut + n) = cyclicShift P w ((start + cut) % P) n := by
  simp only [cyclicShift, Nat.mod_add_mod, Nat.add_assoc]

theorem repeatWord_heading {P : Nat} {w : Nat -> Bool} (hP : 0 < P)
    (hh : (wordTrace w P).2 = .north) (n : Nat) :
    (wordTrace (repeatWord P w) n).2 = (wordTrace w (n % P)).2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < P
    · rw [repeatWord_trace w (by omega), Nat.mod_eq_of_lt hn]
    · have ht := congrArg Prod.snd (repeatWord_trace_period hh (n - P))
      rw [show n - P + P = n by omega] at ht
      rw [ht, ih (n - P) (by omega)]
      congr 2
      exact (Nat.mod_eq_sub_mod (by omega : n >= P)).symm

theorem cyclicShift_heading {P start : Nat} {w : Nat -> Bool}
    (hP : 0 < P) (hh : (wordTrace w P).2 = .north) (hs : start < P) (n : Nat) :
    rotateDir (wordTrace w start).2 (wordTrace (cyclicShift P w start) n).2 =
      (wordTrace w ((start + n) % P)).2 := by
  have ht := congrArg Prod.snd (trace_shift (repeatWord P w) start n)
  rw [repeatWord_heading hP hh, repeatWord_trace w (Nat.le_of_lt hs)] at ht
  exact ht.symm

theorem core_rebase {P : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2,-2)) (c : Core P w) :
    ConsistentWord P (cyclicShift P w c.a0) /\
      exists d0 d1, GateBlocks P w c d0 d1 := by
  have hP : 0 < P := Nat.zero_lt_of_lt c.a0_lt
  have hc := cyclicShift_consistent hw hP c.a0
  refine ⟨hc, ?_⟩
  obtain ⟨d0,d1,hd0,hd1,hperiod,hphase0,hreturn0,hphase1,hreturn1⟩ :=
    core_lengths hw hd c
  have hout := core_outgoing hw c
  have hexit := core_exit_data hw hd c
  have hb := core_bridges hw hd c
  have hr0 : wordPos (repeatWord P w) (c.a0 + d0) =
      wordPos (repeatWord P w) c.a0 := by
    simpa only [ContinuousPhasePath.pos_ofStart hP hw.1, Nat.add_zero] using hreturn0
  have hr1 : wordPos (repeatWord P w) (c.a1 + d1) =
      wordPos (repeatWord P w) c.a1 := by
    simpa only [ContinuousPhasePath.pos_ofStart hP hw.1, Nat.add_zero] using hreturn1
  have hp0 : (c.a0 + d0) % P = Drift.pred P c.b0 := hphase0
  have hp1 : (c.a1 + d1) % P = Drift.pred P c.b1 := hphase1
  have hend0 := bridge_end hP hw.1 c.b0_lt hp0 hr0 hexit.2.2.1 hout.2.2.2 hb.1
  have hfirst : (c.a0 + (d0 + 1)) % P = c.b0 := by
    rw [phase_succ, hp0]
    exact UnitDiagonalMatching.succ_pred c.b0_lt
  have hsecond : (c.a1 + (d1 + 1)) % P = c.b1 := by
    rw [phase_succ, hp1]
    exact UnitDiagonalMatching.succ_pred c.b1_lt
  have hpose (a : Nat) (ha : a < P) (haDir : (wordTrace w a).2 = .south) (n : Nat) :
      wordPos (cyclicShift P w a) n =
        negPoint (subPoint (wordPos (repeatWord P w) (a + n))
          (wordPos (repeatWord P w) a)) := by
    rw [cyclicShift_pos ha, haDir]
    rw [show wordPos (repeatWord P w) a = wordPos w a from
      congrArg Prod.fst (repeatWord_trace w (Nat.le_of_lt ha))]
    rfl
  have ha0 : (wordTrace w c.a0).2 = .south := c.dir0
  have ha1 : (wordTrace w c.a1).2 = .south := c.dir2
  have hzero0 : wordPos (cyclicShift P w c.a0) d0 = (0,0) := by
    rw [hpose c.a0 c.a0_lt ha0, hr0]
    simp [negPoint, subPoint]
  have hzero1 : wordPos (cyclicShift P w c.a1) d1 = (0,0) := by
    rw [hpose c.a1 c.a1_lt ha1, hr1]
    simp [negPoint, subPoint]
  have heast0 : wordPos (cyclicShift P w c.a0) (d0 + 1) = (-1,0) := by
    rw [hpose c.a0 c.a0_lt ha0, repeat_pos_step hP hw.1,
      hp0, hexit.2.2.1, hr0]
    apply Prod.ext <;> simp only [negPoint, subPoint, move] <;> omega
  have heast1 : wordPos (cyclicShift P w c.a1) (d1 + 1) = (-1,0) := by
    rw [hpose c.a1 c.a1_lt ha1, repeat_pos_step hP hw.1,
      hp1, hexit.2.2.2.1, hr1]
    apply Prod.ext <;> simp only [negPoint, subPoint, move] <;> omega
  have hcut : wordPos (cyclicShift P w c.a0) (d0 + 2) = (-1,1) := by
    rw [hpose c.a0 c.a0_lt ha0, hend0.2]
    apply Prod.ext <;> simp only [negPoint, subPoint, addPoint] <;> omega
  have hcutdir : (wordTrace (cyclicShift P w c.a0) (d0 + 2)).2 = .north := by
    have he := cyclicShift_heading hP hw.1 c.a0_lt (d0 + 2)
    rw [ha0, hend0.1, ha1] at he
    cases h : (wordTrace (cyclicShift P w c.a0) (d0 + 2)).2 <;>
      simp [h, rotateDir, Direction.right] at he <;> rfl
  have htail (n : Nat) :
      wordPos (cyclicShift P w c.a0) (d0 + 2 + n) =
        addPoint (-1,1) (wordPos (cyclicShift P w c.a1) n) := by
    have ht := congrArg Prod.fst (trace_shift (cyclicShift P w c.a0) (d0 + 2) n)
    have he : (fun i => cyclicShift P w c.a0 (d0 + 2 + i)) = cyclicShift P w c.a1 := by
      funext i
      rw [shift_add, hend0.1]
    change wordPos (cyclicShift P w c.a0) (d0 + 2 + n) =
      addPoint (wordPos (cyclicShift P w c.a0) (d0 + 2))
        (rotatePoint (wordTrace (cyclicShift P w c.a0) (d0 + 2)).2
          (wordPos (fun i => cyclicShift P w c.a0 (d0 + 2 + i)) n)) at ht
    simpa only [he, hcut, hcutdir, rotatePoint] using ht
  have htphase (n : Nat) : (c.a0 + (d0 + 2 + n)) % P = (c.a1 + n) % P := by
    rw [<- Nat.add_assoc, <- Nat.mod_add_mod (c.a0 + (d0 + 2)), hend0.1]
  refine ⟨d0,d1,⟨hd0,hd1,hperiod,hp0,hfirst,hend0.1,?_,?_,
    hzero0,heast0,hcut,hcutdir,?_,?_,?_⟩⟩
  · rw [htphase, hp1]
  · rw [show d0 + 2 + d1 + 1 = d0 + 2 + (d1 + 1) by omega, htphase, hsecond]
  · rw [htail, hzero1]
    rfl
  · rw [show d0 + 2 + d1 + 1 = d0 + 2 + (d1 + 1) by omega, htail, heast1]
    rfl
  · rw [cyclicShift_drift hw.1 c.a0_lt, ha0, hd]
    rfl

/-! The existing shared-boundary API fixes the southeast coordinate frame.
This is its half-turn transport: the same Block, Support, visits, and Legal
definitions, with the second origin and forward ray rotated by 180 degrees.
In particular the forward ray must be rotated along with the displacement. -/
namespace Northwest

def advance (p : Point) (k : Int) : Point := (p.1 - k, p.2 + k)

@[simp] theorem advance_zero (p : Point) : advance p 0 = p := by
  cases p
  simp [advance]

@[simp] theorem advance_add (p : Point) (k l : Int) :
    advance (advance p k) l = advance p (k + l) := by
  apply Prod.ext <;> simp only [advance] <;> omega

@[simp] theorem neg_advance (p : Point) (k : Int) :
    negPoint (advance p k) = SharedBoundary.advance (negPoint p) k := by
  apply Prod.ext <;> simp only [negPoint, advance, SharedBoundary.advance] <;> omega

private theorem neg_inj (p q : Point) : negPoint p = negPoint q <-> p = q := by
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    apply Prod.ext <;> simp only [negPoint] at hx hy <;> omega
  · exact congrArg negPoint

def onRay (p q : Point) : Bool := SharedBoundary.onRay (negPoint p) (negPoint q)

theorem onRay_iff (p q : Point) :
    onRay p q = true <-> exists j : Nat, q = advance p (2 * (j : Int)) := by
  rw [onRay, SharedBoundary.onRay_iff]
  constructor <;> rintro ⟨j,hj⟩ <;> refine ⟨j,?_⟩
  · apply (neg_inj _ _).mp
    rw [neg_advance]
    exact hj
  · rw [hj, neg_advance]

theorem onRay_translate (p q : Point) (k : Int) :
    onRay (advance p k) (advance q k) = onRay p q := by
  simp only [onRay, neg_advance, SharedBoundary.onRay_translate]

theorem onRay_split (p q : Point) :
    onRay p q = (decide (q = p) || onRay (advance p 2) q) := by
  simp only [onRay, neg_advance, SharedBoundary.onRay_split (negPoint p) (negPoint q),
    neg_inj]

theorem onRay_strict_ne (p q : Point) (h : onRay (advance p 2) q = true) : Not (q = p) := by
  intro he
  have hr : SharedBoundary.onRay (SharedBoundary.advance (negPoint p) 2) (negPoint q) = true := by
    simpa only [onRay, neg_advance] using h
  exact SharedBoundary.onRay_strict_ne _ _ hr (congrArg negPoint he)

def V (w : Nat -> Bool) (P cut : Nat) : Block := ⟨w, cut, P - cut, (-1,1)⟩

@[simp] theorem V_length (w : Nat -> Bool) (P cut : Nat) :
    (V w P cut).length = P - cut := rfl

@[simp] theorem V_color (w : Nat -> Bool) (P cut i : Nat) :
    (V w P cut).color i = w (cut + i) := rfl

@[simp] theorem V_pos (w : Nat -> Bool) (P cut i : Nat) :
    (V w P cut).pos i = advance (wordPos w (cut + i)) (-1) := by
  apply Prod.ext <;> simp only [V, Block.pos, subPoint, advance] <;> omega

def tailCount (b : Block) (p : Point) : Nat :=
  (List.range b.length).countP (fun i => onRay p (b.pos i))

def T (b : Block) (p : Point) : Bool := bit (tailCount b p)

private theorem countP_or {a : Type} (xs : List a) (f g : a -> Bool)
    (h : forall x, x ∈ xs -> f x = true -> g x = false) :
    xs.countP (fun x => f x || g x) = xs.countP f + xs.countP g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      ih (fun y hy => h y (by simp [hy]))]
    have hx := h x (by simp)
    cases hf : f x <;> cases hg : g x <;> simp_all <;> omega

private theorem countP_prefix (n i : Nat) (hi : i <= n) (f : Nat -> Bool) :
    (List.range n).countP (fun j => decide (j < i) && f j) =
      (List.range i).countP f := by
  rw [show n = i + (n - i) by omega, List.range_add, List.countP_append, List.countP_map]
  have hl : (List.range i).countP (fun j => decide (j < i) && f j) =
      (List.range i).countP f := by
    apply List.countP_congr
    intro j hj
    simp [List.mem_range.mp hj]
  have hr : (List.range (n - i)).countP
      ((fun j => decide (j < i) && f j) ∘ (i + ·)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro j _
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq, not_and]
    omega
  rw [hl, hr, Nat.add_zero]

theorem tailCount_split (b : Block) (p : Point) :
    tailCount b p = b.N p + tailCount b (advance p 2) := by
  unfold tailCount Block.N Block.visits
  have he : (fun i => onRay p (b.pos i)) =
      (fun i => decide (b.pos i = p) || onRay (advance p 2) (b.pos i)) := by
    funext i
    exact onRay_split p (b.pos i)
  rw [he]
  apply countP_or
  intro i _ hi
  apply Bool.eq_false_iff.mpr
  intro hr
  exact onRay_strict_ne _ _ hr (of_decide_eq_true hi)

theorem whole_tail_split {P cut : Nat} (hc : cut <= P) (w : Nat -> Bool) (p : Point) :
    tailCount (U w P) p = tailCount (U w cut) p +
      tailCount (V w P cut) (advance p (-1)) := by
  simp only [tailCount, U_pos, V_pos, onRay_translate, U_length, V_length]
  conv => lhs; rw [show P = cut + (P - cut) by omega]
  rw [List.range_add, List.countP_append, List.countP_map]
  rfl

theorem whole_visits_split (w : Nat -> Bool) (P cut i : Nat) (p : Point) :
    (U w P).visits (cut + i) p = (U w cut).N p +
      (V w P cut).visits i (advance p (-1)) := by
  simp only [Block.N, Block.visits, U_length, U_pos, V_pos, List.range_add,
    List.countP_append, List.countP_map]
  congr 1
  apply List.countP_congr
  intro j _
  simp only [Function.comp_apply, decide_eq_true_eq]
  constructor
  · intro he
    rw [he]
  · intro he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    apply Prod.ext <;> simp only [advance] at hx hy <;> omega

private theorem earlier_iff_ray (w : Nat -> Bool) (i j : Nat) :
    EarlierPhase (wordPos w) (-2,2) i j <->
      (j < i /\ wordPos w j = wordPos w i) \/
        onRay (advance (wordPos w i) 2) (wordPos w j) = true := by
  rw [EarlierPhase, onRay_iff]
  apply or_congr_right
  constructor
  · rintro ⟨t,ht,he⟩
    refine ⟨t - 1,?_⟩
    rw [he]
    apply Prod.ext <;> simp only [addPoint, scalePoint, advance] <;> omega
  · rintro ⟨t,he⟩
    refine ⟨t + 1,by omega,?_⟩
    rw [he]
    apply Prod.ext <;> simp only [addPoint, scalePoint, advance, Int.natCast_add,
      Int.natCast_one] <;> omega

theorem stableRank_eq_visits_add_tail {P i : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (-2,2)) (hi : i < P) :
    Drift.stableRank P w i = (U w P).visits i (wordPos w i) +
      tailCount (U w P) (advance (wordPos w i) 2) := by
  rw [Drift.stableRank, priorPhases, <- List.countP_eq_length_filter, hd]
  have he : (List.range P).countP (checkEarlierPhase (wordPos w) (-2,2) i) =
      (List.range P).countP (fun j =>
        (decide (j < i) && decide (wordPos w j = wordPos w i)) ||
          onRay (advance (wordPos w i) 2) (wordPos w j)) := by
    apply List.countP_congr
    intro j _
    rw [checkEarlierPhase_iff (by decide), earlier_iff_ray]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [he, countP_or, countP_prefix P i (by omega)]
  · simp only [Block.visits, tailCount, U_length, U_pos]
  · intro j _ hj
    have hp : wordPos w j = wordPos w i :=
      (show j < i /\ wordPos w j = wordPos w i from
        by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hj).2
    apply Bool.eq_false_iff.mpr
    intro hr
    exact onRay_strict_ne _ _ hr hp

theorem stableRank_U {P cut i : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (-2,2)) (hc : cut <= P) (hi : i < cut) :
    Drift.stableRank P w i = (U w cut).visits i ((U w cut).pos i) +
      tailCount (U w cut) (advance ((U w cut).pos i) 2) +
        tailCount (V w P cut) (advance ((U w cut).pos i) 1) := by
  rw [stableRank_eq_visits_add_tail hd (by omega), whole_tail_split hc]
  simp only [U_pos, advance_add]
  exact Nat.add_assoc _ _ _ |>.symm

theorem stableRank_V {P cut i : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (-2,2)) (hc : cut <= P) (hi : i < P - cut) :
    Drift.stableRank P w (cut + i) =
      (V w P cut).visits i ((V w P cut).pos i) +
        tailCount (U w cut) (advance ((V w P cut).pos i) 1) +
          tailCount (V w P cut) (advance ((V w P cut).pos i) 2) := by
  rw [stableRank_eq_visits_add_tail hd (by omega), whole_visits_split, whole_tail_split hc]
  simp only [V_pos, advance_add]
  have h := tailCount_split (U w cut) (wordPos w (cut + i))
  simp only [show (-1 : Int) + 1 = 0 by decide, advance_zero,
    show (-1 : Int) + 2 = 1 by decide, show (2 : Int) + -1 = 1 by decide]
  omega

def initialU (w : Nat -> Bool) (P cut : Nat) : Board := fun p =>
  T (U w cut) (advance p 2) ^^ T (V w P cut) (advance p 1)

def initialV (w : Nat -> Bool) (P cut : Nat) : Board := fun p =>
  T (V w P cut) (advance p 2) ^^ T (U w cut) (advance p 1)

theorem stableRank_U_bit {P cut i : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (-2,2)) (hc : cut <= P) (hi : i < cut) :
    bit (Drift.stableRank P w i) =
      (initialU w P cut ((U w cut).pos i) ^^ bit ((U w cut).visits i ((U w cut).pos i))) := by
  rw [stableRank_U hd hc hi, bit_add, bit_add]
  unfold initialU T
  rw [Bool.xor_assoc]
  exact Bool.xor_comm ..

theorem stableRank_V_bit {P cut i : Nat} {w : Nat -> Bool}
    (hd : wordDrift P w = (-2,2)) (hc : cut <= P) (hi : i < P - cut) :
    bit (Drift.stableRank P w (cut + i)) =
      (initialV w P cut ((V w P cut).pos i) ^^
        bit ((V w P cut).visits i ((V w P cut).pos i))) := by
  rw [stableRank_V hd hc hi, bit_add, bit_add]
  unfold initialV T
  rw [Bool.xor_assoc, Bool.xor_comm (bit (tailCount (U w cut) _))]
  exact Bool.xor_comm ..

theorem consistentWord_iff_initial_legal {P cut : Nat} {w : Nat -> Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (-2,2)) (hc : cut <= P) :
    ConsistentWord P w <->
      (U w cut).Legal (initialU w P cut) /\ (V w P cut).Legal (initialV w P cut) := by
  constructor
  · intro hw
    constructor
    · intro i hi
      rw [U_color]
      exact (Drift.consistentWord_stableRank_color hw (Nat.lt_of_lt_of_le hi hc)).trans
        (stableRank_U_bit hd hc hi)
    · intro i hi
      change w (cut + i) = _
      exact (Drift.consistentWord_stableRank_color hw
        (by change i < P - cut at hi; omega)).trans (stableRank_V_bit hd hc hi)
  · rintro ⟨hu,hv⟩
    refine ⟨hdir, by rw [hd]; decide, ?_⟩
    intro i hi
    change w i = bit (Drift.stableRank P w i)
    by_cases hicut : i < cut
    · rw [stableRank_U_bit hd hc hicut]
      simpa only [U_color] using hu i hicut
    · have hik : i - cut < P - cut := by omega
      have he : cut + (i - cut) = i := by omega
      have hread := hv (i - cut) hik
      have hrank := stableRank_V_bit hd hc hik
      change w (cut + (i - cut)) = _ at hread
      rw [he] at hread hrank
      exact hread.trans hrank.symm

/-- The two shared-boundary equations, with d=(-1,1). -/
def Boundary (w : Nat -> Bool) (P cut : Nat) (aU aV : Board) : Prop :=
  (forall p, (U w cut).Support p ->
    T (V w P cut) (advance p 1) = (aU p ^^ T (U w cut) (advance p 2))) /\
  (forall p, (V w P cut).Support p ->
    T (U w cut) (advance p 1) = (aV p ^^ T (V w P cut) (advance p 2)))

theorem boundary_iff_boards (w : Nat -> Bool) (P cut : Nat) (aU aV : Board) :
    Boundary w P cut aU aV <->
      (forall p, (U w cut).Support p -> initialU w P cut p = aU p) /\
      (forall p, (V w P cut).Support p -> initialV w P cut p = aV p) := by
  have xor_solve (x y a : Bool) : (x ^^ y) = a <-> y = (a ^^ x) := by
    cases x <;> cases y <;> cases a <;> decide
  simp only [Boundary, initialU, initialV, xor_solve]

theorem consistentWord_iff_sharedBoundary {P cut : Nat} {w : Nat -> Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (-2,2))
    (hc : cut <= P) {aU aV : Board}
    (hu : (U w cut).Legal aU) (hv : (V w P cut).Legal aV) :
    ConsistentWord P w <-> Boundary w P cut aU aV := by
  rw [consistentWord_iff_initial_legal hdir hd hc, boundary_iff_boards]
  constructor
  · rintro ⟨hU,hV⟩
    exact ⟨fun _ hp => Block.legal_unique_on_support hU hu hp,
      fun _ hp => Block.legal_unique_on_support hV hv hp⟩
  · rintro ⟨hU,hV⟩
    exact ⟨(Block.legal_congr_on_support hU).mpr hu, (Block.legal_congr_on_support hV).mpr hv⟩

theorem consistentWord_iff_exists_sharedBoundary {P cut : Nat} {w : Nat -> Bool}
    (hdir : (wordTrace w P).2 = .north) (hd : wordDrift P w = (-2,2)) (hc : cut <= P) :
    ConsistentWord P w <-> exists aU aV : Board,
      (U w cut).Legal aU /\ (V w P cut).Legal aV /\ Boundary w P cut aU aV := by
  constructor
  · intro hw
    obtain ⟨hu,hv⟩ := (consistentWord_iff_initial_legal hdir hd hc).mp hw
    refine ⟨initialU w P cut,initialV w P cut,hu,hv,?_⟩
    exact (boundary_iff_boards ..).mpr ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  · rintro ⟨aU,aV,hu,hv,hb⟩
    exact (consistentWord_iff_sharedBoundary hdir hd hc hu hv).mpr hb

theorem two_block_displacements {P cut : Nat} {w : Nat -> Bool}
    (hc : cut <= P) (hd : wordDrift P w = (-2,2)) (hcut : wordPos w cut = (-1,1)) :
    (U w cut).pos 0 = (0,0) /\ (U w cut).pos cut = (-1,1) /\
      (V w P cut).pos 0 = (0,0) /\ (V w P cut).pos (P-cut) = (-1,1) := by
  simp only [U_pos, V_pos, Nat.add_zero, show cut + (P - cut) = P by omega,
    hcut, show wordPos w P = (-2,2) from hd]
  simp [wordPos, wordTrace, advance]

end Northwest

/-- The second block reads the cyclic word starting at a1, at every index. -/
theorem GateBlocks.second_color {P d0 d1 : Nat} {w : Nat -> Bool} {c : Core P w}
    (hg : GateBlocks P w c d0 d1) (i : Nat) :
    (Northwest.V (cyclicShift P w c.a0) P (d0 + 2)).color i = cyclicShift P w c.a1 i := by
  rw [Northwest.V_color, shift_add, hg.cut_phase]

/-- The second block has exactly the independently normalized trace at a1.
This identifies every intermediate position, not just its displacement. -/
theorem GateBlocks.second_pos {P d0 d1 : Nat} {w : Nat -> Bool} {c : Core P w}
    (hg : GateBlocks P w c d0 d1) (i : Nat) :
    (Northwest.V (cyclicShift P w c.a0) P (d0 + 2)).pos i =
      wordPos (cyclicShift P w c.a1) i := by
  have ht := congrArg Prod.fst (trace_shift (cyclicShift P w c.a0) (d0 + 2) i)
  have he : (fun j => cyclicShift P w c.a0 (d0 + 2 + j)) = cyclicShift P w c.a1 := by
    funext j
    rw [shift_add, hg.cut_phase]
  change wordPos (cyclicShift P w c.a0) (d0 + 2 + i) =
    addPoint (wordPos (cyclicShift P w c.a0) (d0 + 2))
      (rotatePoint (wordTrace (cyclicShift P w c.a0) (d0 + 2)).2
        (wordPos (fun j => cyclicShift P w c.a0 (d0 + 2 + j)) i)) at ht
  rw [he, hg.cut_pos, hg.cut_heading] at ht
  rw [Northwest.V_pos, ht]
  apply Prod.ext <;> simp only [Northwest.advance, addPoint, rotatePoint] <;> omega

theorem GateBlocks.block_lengths {P d0 d1 : Nat} {w : Nat -> Bool} {c : Core P w}
    (hg : GateBlocks P w c d0 d1) :
    (U (cyclicShift P w c.a0) (d0 + 2)).length = d0 + 2 /\
      (Northwest.V (cyclicShift P w c.a0) P (d0 + 2)).length = d1 + 2 := by
  constructor
  · rfl
  · change P - (d0 + 2) = d1 + 2
    have := hg.period_eq
    omega

theorem GateBlocks.block_displacements {P d0 d1 : Nat} {w : Nat -> Bool} {c : Core P w}
    (hg : GateBlocks P w c d0 d1) :
    let u := cyclicShift P w c.a0
    (U u (d0 + 2)).pos 0 = (0,0) /\ (U u (d0 + 2)).pos (d0 + 2) = (-1,1) /\
      (Northwest.V u P (d0 + 2)).pos 0 = (0,0) /\
      (Northwest.V u P (d0 + 2)).pos (d1 + 2) = (-1,1) := by
  have hc : d0 + 2 <= P := by have := hg.period_eq; omega
  have hn : P - (d0 + 2) = d1 + 2 := by have := hg.period_eq; omega
  simpa only [hn] using Northwest.two_block_displacements hc hg.drift hg.cut_pos

/-- Rebasing any specified core constructs legal boards satisfying both
shared-boundary equations in the actual normalized northwest frame. -/
theorem core_rebase_sharedBoundary {P : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2,-2)) (c : Core P w) :
    exists d0 d1, GateBlocks P w c d0 d1 /\
      let u := cyclicShift P w c.a0
      let cut := d0 + 2
      ConsistentWord P u /\
        (U u cut).Legal (Northwest.initialU u P cut) /\
        (Northwest.V u P cut).Legal (Northwest.initialV u P cut) /\
        Northwest.Boundary u P cut (Northwest.initialU u P cut) (Northwest.initialV u P cut) := by
  obtain ⟨hc,d0,d1,hg⟩ := core_rebase hw hd c
  have hcut : d0 + 2 <= P := by have := hg.period_eq; omega
  obtain ⟨hu,hv⟩ := (Northwest.consistentWord_iff_initial_legal hc.1 hg.drift hcut).mp hc
  exact ⟨d0,d1,hg,hc,hu,hv,
    (Northwest.consistentWord_iff_sharedBoundary hc.1 hg.drift hcut hu hv).mp hc⟩

/-- Every consistent southeast word admits the two gate blocks and the full
shared-boundary criterion after cyclic rebasing. The north-heading word has
drift (-2,2); its equal-displacement blocks have d=(-1,1). -/
theorem exists_gate_rebase_sharedBoundary {P : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hP : 0 < P) (hd : wordDrift P w = (2,-2)) :
    exists c : Core P w, exists d0 d1, GateBlocks P w c d0 d1 /\
      let u := cyclicShift P w c.a0
      let cut := d0 + 2
      ConsistentWord P u /\
        (U u cut).Legal (Northwest.initialU u P cut) /\
        (Northwest.V u P cut).Legal (Northwest.initialV u P cut) /\
        Northwest.Boundary u P cut (Northwest.initialU u P cut) (Northwest.initialV u P cut) := by
  obtain ⟨c⟩ := exists_core hw hP hd
  exact ⟨c, core_rebase_sharedBoundary hw hd c⟩

/-- If a rebase already starts north, the original southeast API applies
literally, without rotating either the second block origin or its rays. -/
theorem north_rebase_sharedBoundary {P start cut : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (2,-2)) (hs : start < P)
    (hdir : (wordTrace w start).2 = .north) (hc : cut <= P)
    (hcut : subPoint (wordPos (repeatWord P w) (start + cut)) (wordPos w start) = (1,-1)) :
    let u := cyclicShift P w start
    wordPos u cut = (1,-1) /\ wordDrift P u = (2,-2) /\
      exists aU aV : Board, (U u cut).Legal aU /\ (SharedBoundary.V u P cut).Legal aV /\
        SharedBoundary.SharedBoundary u P cut aU aV := by
  have hp : wordPos (cyclicShift P w start) cut = (1,-1) := by
    rw [cyclicShift_pos hs, hcut, hdir]
    rfl
  have hdr : wordDrift P (cyclicShift P w start) = (2,-2) := by
    rw [cyclicShift_drift hw.1 hs, hdir, hd]
    rfl
  have hw' := cyclicShift_consistent hw (Nat.zero_lt_of_lt hs) start
  exact ⟨hp,hdr,(SharedBoundary.consistentWord_iff_exists_sharedBoundary hw'.1 hdr hc).mp hw'⟩

/-- Non-vacuity follows from the kernel-certified 104-step standard word. -/
theorem stdHighwaySE_nonvacuity :
    exists c : Core 104 TwoCellDiagonal.stdHighwaySE, exists d0 d1,
      GateBlocks 104 TwoCellDiagonal.stdHighwaySE c d0 d1 /\
      let u := cyclicShift 104 TwoCellDiagonal.stdHighwaySE c.a0
      let cut := d0 + 2
      ConsistentWord 104 u /\
        (U u cut).Legal (Northwest.initialU u 104 cut) /\
        (Northwest.V u 104 cut).Legal (Northwest.initialV u 104 cut) /\
        Northwest.Boundary u 104 cut (Northwest.initialU u 104 cut) (Northwest.initialV u 104 cut) :=
  exists_gate_rebase_sharedBoundary TwoCellDiagonal.stdHighwaySE_consistent (by decide)
    TwoCellDiagonal.stdHighwaySE_drift

set_option maxRecDepth 8192 in
/-- An explicit core of the standard word. All four ranks and predecessor
edges are checked by kernel reduction. -/
def stdCore : Core 104 TwoCellDiagonal.stdHighwaySE where
  a0 := 16
  b1 := 15
  a1 := 26
  b0 := 25
  a0_lt := by decide
  b1_lt := by decide
  a1_lt := by decide
  b0_lt := by decide
  a0_rank := by decide +kernel
  b1_rank := by decide +kernel
  a1_rank := by decide +kernel
  b0_rank := by decide +kernel
  edge0 := by decide +kernel
  edge1 := by decide +kernel
  edge2 := by decide +kernel
  edge3 := by decide +kernel
  dir0 := by decide +kernel
  dir1 := by decide +kernel
  dir2 := by decide +kernel
  dir3 := by decide +kernel

set_option maxRecDepth 8192 in
/-- The explicit cut is 10; the closed runs have lengths 8 and 92, and the
second run crosses the original period seam. -/
theorem stdHighwaySE_explicit_blocks : GateBlocks 104 TwoCellDiagonal.stdHighwaySE stdCore 8 92 := by
  constructor <;> decide +kernel

theorem stdHighwaySE_explicit_boundary :
    let u := cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16
    ConsistentWord 104 u /\ wordDrift 104 u = (-2,2) /\ wordPos u 10 = (-1,1) /\
      (U u 10).Legal (Northwest.initialU u 104 10) /\
      (Northwest.V u 104 10).Legal (Northwest.initialV u 104 10) /\
      Northwest.Boundary u 104 10 (Northwest.initialU u 104 10) (Northwest.initialV u 104 10) := by
  have hw := cyclicShift_consistent TwoCellDiagonal.stdHighwaySE_consistent (by decide) 16
  have hg := stdHighwaySE_explicit_blocks
  have hd : wordDrift 104 (cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16) = (-2,2) := hg.drift
  have hp : wordPos (cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16) 10 = (-1,1) := hg.cut_pos
  obtain ⟨hu,hv⟩ := (Northwest.consistentWord_iff_initial_legal hw.1 hd (by decide : 10 <= 104)).mp hw
  exact ⟨hw,hd,hp,hu,hv,(Northwest.consistentWord_iff_sharedBoundary hw.1 hd (by decide) hu hv).mp hw⟩

end LangtonsAnt.PersistA.GateRebase
