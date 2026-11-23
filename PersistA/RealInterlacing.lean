import PersistA.GateRebase

/-!
Strict interlacing for the actual gate blocks of a consistent word.

All coordinates below are the normalized northwest coordinates of GateRebase:
d = (-1,1), layer = x+y, lane = x mod 2, and forward order is increasing -x.
Each block uses its own origin, as in Northwest.Boundary. The supplying visits
are on the opposite lane. Counting both lanes would be a different statement.
No value of an initial board at a hole in the support is used.
-/

namespace LangtonsAnt.PersistA.RealInterlacing

open SharedBoundary GateRebase

/-- Same layer, same lane, and strictly forward along d = (-1,1). -/
def SameLayerLaneBefore (a b : Point) : Prop :=
  a.1 + a.2 = b.1 + b.2 /\ a.1 % 2 = b.1 % 2 /\ b.1 < a.1

/-- The strict segment on the supplying (opposite) lane, in local coordinates. -/
def OppositeBetween (a b q : Point) : Prop :=
  q.1 + q.2 = a.1 + a.2 /\ q.1 % 2 ≠ a.1 % 2 /\ b.1 < q.1 /\ q.1 < a.1

instance (a b q : Point) : Decidable (OppositeBetween a b q) :=
  inferInstanceAs (Decidable
    (q.1 + q.2 = a.1 + a.2 /\ q.1 % 2 ≠ a.1 % 2 /\ b.1 < q.1 /\ q.1 < a.1))

/-- Individual real visits, with multiplicity, on the specified open segment. -/
def openVisits (v : Block) (a b : Point) : Nat :=
  (List.range v.length).countP (fun i => decide (OppositeBetween a b (v.pos i)))

/-- The board is used only at support points in the theorems below. -/
def demand (u : Block) (initial : Board) (p : Point) : Bool :=
  initial p ^^ Northwest.T u (Northwest.advance p 2)

theorem sameLayerLaneBefore_iff (a b : Point) :
    SameLayerLaneBefore a b <->
      exists n : Nat, 0 < n /\ b = Northwest.advance a (2 * (n : Int)) := by
  constructor
  · rintro ⟨hl, hp, hb⟩
    refine ⟨((a.1 - b.1) / 2).toNat, by omega, ?_⟩
    apply Prod.ext <;> simp only [Northwest.advance] <;> omega
  · rintro ⟨n, hn, rfl⟩
    simp only [SameLayerLaneBefore, Northwest.advance]
    omega

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

theorem ray_open_split {a b : Point} (hab : SameLayerLaneBefore a b) (q : Point) :
    Northwest.onRay (Northwest.advance a 1) q =
      (decide (OppositeBetween a b q) || Northwest.onRay (Northwest.advance b 1) q) := by
  apply Bool.eq_iff_iff.mpr
  change (Northwest.onRay (Northwest.advance a 1) q = true) <-> _
  simp only [Bool.or_eq_true, Northwest.onRay, SharedBoundary.onRay, decide_eq_true_eq]
  simp only [negPoint, Northwest.advance, OppositeBetween]
  rcases hab with ⟨hl, hp, hb⟩
  omega

/-- The two tails differ by exactly the actual visits on the open segment. -/
theorem tailCount_open_split (v : Block) {a b : Point} (hab : SameLayerLaneBefore a b) :
    Northwest.tailCount v (Northwest.advance a 1) =
      openVisits v a b + Northwest.tailCount v (Northwest.advance b 1) := by
  unfold Northwest.tailCount openVisits
  have he : (fun i => Northwest.onRay (Northwest.advance a 1) (v.pos i)) =
      (fun i => decide (OppositeBetween a b (v.pos i)) ||
        Northwest.onRay (Northwest.advance b 1) (v.pos i)) := by
    funext i
    exact ray_open_split hab _
  rw [he]
  apply countP_or
  intro i _ hi
  apply Bool.eq_false_iff.mpr
  intro hr
  have hs := of_decide_eq_true hi
  have ht := of_decide_eq_true hr
  simp only [OppositeBetween] at hs
  simp only [negPoint, Northwest.advance] at ht
  omega

theorem tail_xor_eq_openVisits (v : Block) {a b : Point} (hab : SameLayerLaneBefore a b) :
    (Northwest.T v (Northwest.advance a 1) ^^ Northwest.T v (Northwest.advance b 1)) =
      bit (openVisits v a b) := by
  simp only [Northwest.T, tailCount_open_split v hab, bit_add,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- A finite literal sum of visit multiplicities, with its exact tail remainder. -/
theorem tailCount_sum (v : Block) (p : Point) (n : Nat) :
    Northwest.tailCount v p =
      ((List.range n).map (fun j : Nat => v.N (Northwest.advance p (2 * (j : Int))))).sum +
        Northwest.tailCount v (Northwest.advance p (2 * (n : Int))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [ih, Northwest.tailCount_split v (Northwest.advance p (2 * (n : Int))),
      Northwest.advance_add]
    have he : 2 * (n : Int) + 2 = 2 * ((n + 1 : Nat) : Int) := by omega
    rw [he]
    omega

/-- The interval count also equals the sum over its opposite-lane physical cells. -/
theorem openVisits_eq_sum (v : Block) (a : Point) (n : Nat) (hn : 0 < n) :
    openVisits v a (Northwest.advance a (2 * (n : Int))) =
      ((List.range n).map
        (fun j : Nat => v.N (Northwest.advance a (2 * (j : Int) + 1)))).sum := by
  have hsplit := tailCount_open_split v
    ((sameLayerLaneBefore_iff a (Northwest.advance a (2 * (n : Int)))).mpr ⟨n, hn, rfl⟩)
  have hsum := tailCount_sum v (Northwest.advance a 1) n
  simp only [Northwest.advance_add] at hsplit hsum
  simp only [Int.add_comm 1] at hsum
  omega

private theorem odd_sum_has_odd (xs : List Nat) (h : bit xs.sum = true) :
    exists n, n ∈ xs /\ bit n = true := by
  induction xs with
  | nil => simp [bit] at h
  | cons n ns ih =>
    cases hn : bit n with
    | false =>
      have ht : bit ns.sum = true := by
        simpa only [List.sum_cons, bit_add, hn, Bool.false_xor] using h
      obtain ⟨m, hm, ho⟩ := ih ht
      exact ⟨m, List.mem_cons_of_mem n hm, ho⟩
    | true => exact ⟨n, by simp, hn⟩

/-- Odd total visits force a physical cell with odd visit multiplicity. -/
theorem odd_openVisits_has_odd_support (v : Block) {a b : Point}
    (hab : SameLayerLaneBefore a b) (hodd : openVisits v a b % 2 = 1) :
    exists q, v.Support q /\ OppositeBetween a b q /\ v.N q % 2 = 1 := by
  obtain ⟨n, hn, rfl⟩ := (sameLayerLaneBefore_iff a b).mp hab
  rw [openVisits_eq_sum v a n hn] at hodd
  have hbit : bit (((List.range n).map
      (fun j : Nat => v.N (Northwest.advance a (2 * (j : Int) + 1)))).sum) = true := by
    simpa only [bit, decide_eq_true_eq] using hodd
  obtain ⟨m, hm, ho⟩ := odd_sum_has_odd _ hbit
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
  have hjn := List.mem_range.mp hj
  rw [<- he] at ho
  have hmod : v.N (Northwest.advance a (2 * (j : Int) + 1)) % 2 = 1 :=
    of_decide_eq_true ho
  refine ⟨Northwest.advance a (2 * (j : Int) + 1), ?_, ?_, hmod⟩
  · apply (v.support_iff _).mpr
    omega
  · simp only [OppositeBetween, Northwest.advance]
    omega

/-- Exact parity identity at any two supported endpoints; holes are unrestricted. -/
theorem demand_xor_eq_openVisits {u v : Block} {initial : Board}
    (hboundary : forall p, u.Support p ->
      Northwest.T v (Northwest.advance p 1) = demand u initial p)
    {a b : Point} (ha : u.Support a) (hb : u.Support b)
    (hab : SameLayerLaneBefore a b) :
    (demand u initial a ^^ demand u initial b) = bit (openVisits v a b) := by
  rw [<- hboundary a ha, <- hboundary b hb]
  exact tail_xor_eq_openVisits v hab

/-- Both total oddness and a genuine odd-multiplicity physical witness. -/
def StrictInterlacing (u v : Block) (initial : Board) : Prop :=
  forall a b, u.Support a -> u.Support b -> SameLayerLaneBefore a b ->
    demand u initial a ≠ demand u initial b ->
      openVisits v a b % 2 = 1 /\
        exists q, v.Support q /\ OppositeBetween a b q /\ v.N q % 2 = 1

theorem strict_interlacing_of_boundary {u v : Block} {initial : Board}
    (hboundary : forall p, u.Support p ->
      Northwest.T v (Northwest.advance p 1) = demand u initial p) :
    StrictInterlacing u v initial := by
  intro a b ha hb hab hne
  have hx := demand_xor_eq_openVisits hboundary ha hb hab
  have ho : bit (openVisits v a b) = true := by
    rw [<- hx]
    cases hda : demand u initial a <;> cases hdb : demand u initial b <;> simp_all
  have hmod : openVisits v a b % 2 = 1 := of_decide_eq_true ho
  exact ⟨hmod, odd_openVisits_has_odd_support v hab hmod⟩

theorem boundary_U_demand_parity {P cut : Nat} {w : Nat -> Bool} {aU aV : Board}
    (h : Northwest.Boundary w P cut aU aV) {a b : Point}
    (ha : (U w cut).Support a) (hb : (U w cut).Support b)
    (hab : SameLayerLaneBefore a b) :
    (demand (U w cut) aU a ^^ demand (U w cut) aU b) =
      bit (openVisits (Northwest.V w P cut) a b) :=
  demand_xor_eq_openVisits h.1 ha hb hab

theorem boundary_V_demand_parity {P cut : Nat} {w : Nat -> Bool} {aU aV : Board}
    (h : Northwest.Boundary w P cut aU aV) {a b : Point}
    (ha : (Northwest.V w P cut).Support a) (hb : (Northwest.V w P cut).Support b)
    (hab : SameLayerLaneBefore a b) :
    (demand (Northwest.V w P cut) aV a ^^ demand (Northwest.V w P cut) aV b) =
      bit (openVisits (U w cut) a b) :=
  demand_xor_eq_openVisits h.2 ha hb hab

theorem boundary_strict_interlacing {P cut : Nat} {w : Nat -> Bool} {aU aV : Board}
    (h : Northwest.Boundary w P cut aU aV) :
    StrictInterlacing (U w cut) (Northwest.V w P cut) aU /\
      StrictInterlacing (Northwest.V w P cut) (U w cut) aV :=
  ⟨strict_interlacing_of_boundary h.1, strict_interlacing_of_boundary h.2⟩

/-- Any legal boards for a consistent northwest word satisfy both constraints. -/
theorem consistentWord_strict_interlacing {P cut : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (-2,2)) (hc : cut <= P)
    {aU aV : Board} (hu : (U w cut).Legal aU) (hv : (Northwest.V w P cut).Legal aV) :
    StrictInterlacing (U w cut) (Northwest.V w P cut) aU /\
      StrictInterlacing (Northwest.V w P cut) (U w cut) aV :=
  boundary_strict_interlacing
    ((Northwest.consistentWord_iff_sharedBoundary hw.1 hd hc hu hv).mp hw)

/-- Any specified actual gate decomposition, with arbitrary legal initial boards. -/
theorem gate_rebase_strict_interlacing {P d0 d1 : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) {c : FirstVisitCycle.Core P w}
    (hg : GateBlocks P w c d0 d1) {aU aV : Board}
    (hu : (U (cyclicShift P w c.a0) (d0 + 2)).Legal aU)
    (hv : (Northwest.V (cyclicShift P w c.a0) P (d0 + 2)).Legal aV) :
    let u := cyclicShift P w c.a0
    StrictInterlacing (U u (d0 + 2)) (Northwest.V u P (d0 + 2)) aU /\
      StrictInterlacing (Northwest.V u P (d0 + 2)) (U u (d0 + 2)) aV := by
  have hcut : d0 + 2 <= P := by have := hg.period_eq; omega
  exact consistentWord_strict_interlacing
    (cyclicShift_consistent hw (Nat.zero_lt_of_lt c.a0_lt) c.a0) hg.drift hcut hu hv

/-- End-to-end: every original consistent (2,-2) word has actual rebased blocks
with legal boards, both boundary equations, and both strict interlacing laws. -/
theorem exists_gate_rebase_strict_interlacing {P : Nat} {w : Nat -> Bool}
    (hw : ConsistentWord P w) (hP : 0 < P) (hd : wordDrift P w = (2,-2)) :
    exists c : FirstVisitCycle.Core P w, exists d0 d1, GateBlocks P w c d0 d1 /\
      let u := cyclicShift P w c.a0
      let cut := d0 + 2
      ConsistentWord P u /\
        (U u cut).Legal (Northwest.initialU u P cut) /\
        (Northwest.V u P cut).Legal (Northwest.initialV u P cut) /\
        Northwest.Boundary u P cut (Northwest.initialU u P cut) (Northwest.initialV u P cut) /\
        StrictInterlacing (U u cut) (Northwest.V u P cut) (Northwest.initialU u P cut) /\
        StrictInterlacing (Northwest.V u P cut) (U u cut) (Northwest.initialV u P cut) := by
  obtain ⟨c, d0, d1, hg, hw', hu, hv, hb⟩ :=
    exists_gate_rebase_sharedBoundary hw hP hd
  obtain ⟨hiU, hiV⟩ := boundary_strict_interlacing hb
  exact ⟨c, d0, d1, hg, hw', hu, hv, hb, hiU, hiV⟩

/-- The explicit standard core has cut 10, with block lengths 10 and 94. -/
theorem stdHighwaySE_explicit_interlacing :
    let u := cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16
    StrictInterlacing (U u 10) (Northwest.V u 104 10) (Northwest.initialU u 104 10) /\
      StrictInterlacing (Northwest.V u 104 10) (U u 10) (Northwest.initialV u 104 10) := by
  have hb := stdHighwaySE_explicit_boundary
  exact gate_rebase_strict_interlacing TwoCellDiagonal.stdHighwaySE_consistent
    stdHighwaySE_explicit_blocks hb.2.2.2.1 hb.2.2.2.2.1

set_option maxRecDepth 8192 in
/-- Kernel-computed data for an actual demand switch in the long standard block. -/
theorem stdHighwaySE_window_data :
    let u := cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16
    (Northwest.V u 104 10).Support (1,-3) /\
      (Northwest.V u 104 10).Support (-1,-1) /\
      SameLayerLaneBefore (1,-3) (-1,-1) /\
      demand (Northwest.V u 104 10) (Northwest.initialV u 104 10) (1,-3) = true /\
      demand (Northwest.V u 104 10) (Northwest.initialV u 104 10) (-1,-1) = false /\
      openVisits (U u 10) (1,-3) (-1,-1) = 1 /\
      (U u 10).N (0,-2) = 1 /\ OppositeBetween (1,-3) (-1,-1) (0,-2) := by
  dsimp only
  refine ⟨(Block.support_iff _ _).mpr ?_, (Block.support_iff _ _).mpr ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · unfold SameLayerLaneBefore
    decide +kernel

/-- A non-vacuous application of the general theorem, with a concrete odd cell. -/
theorem stdHighwaySE_nonvacuity :
    let u := cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16
    (Northwest.V u 104 10).Support (1,-3) /\
      (Northwest.V u 104 10).Support (-1,-1) /\
      SameLayerLaneBefore (1,-3) (-1,-1) /\
      demand (Northwest.V u 104 10) (Northwest.initialV u 104 10) (1,-3) ≠
        demand (Northwest.V u 104 10) (Northwest.initialV u 104 10) (-1,-1) /\
      openVisits (U u 10) (1,-3) (-1,-1) % 2 = 1 /\
      (U u 10).Support (0,-2) /\ OppositeBetween (1,-3) (-1,-1) (0,-2) /\
      (U u 10).N (0,-2) % 2 = 1 := by
  obtain ⟨ha, hb, hab, hda, hdb, _, hN, hbetween⟩ := stdHighwaySE_window_data
  have hne : demand (Northwest.V (cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16) 104 10)
      (Northwest.initialV (cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16) 104 10) (1,-3) ≠
      demand (Northwest.V (cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16) 104 10)
        (Northwest.initialV (cyclicShift 104 TwoCellDiagonal.stdHighwaySE 16) 104 10) (-1,-1) := by
    rw [hda, hdb]
    decide
  have hodd := stdHighwaySE_explicit_interlacing.2 (1,-3) (-1,-1) ha hb hab hne
  exact ⟨ha, hb, hab, hne, hodd.1, (Block.support_iff _ _).mpr (by omega),
    hbetween, by omega⟩

end LangtonsAnt.PersistA.RealInterlacing
