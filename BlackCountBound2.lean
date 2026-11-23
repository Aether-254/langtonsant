import BlackCountBound

/-!
# The unconditional finite-prefix black-count bound

`black_bound_suffix` proves C2 with the original denominator `2^W`.
The proof avoids defining arbitrary predictor cycles: equal read suffixes give
rigidly congruent finite caches; an event-free segment evolves those caches by
real ant steps; a finite board cannot return to a rigid copy of itself.
Four iterations of such a return give a translation return, contradicting the
proved positive growth of finite-support highways. Thus every `2^W`-step block
has a miss or a black eviction. Exact accounting then gives the desired bound.

The earlier full-key lemmas are also retained, with their distinct, larger
denominator. Neither proof assumes an eventual periodic tail of the input orbit.
-/

namespace LangtonsAnt.BlackCountBound

def cacheState (s : State) (W n : Nat) : FiniteState :=
  { black := cacheLive s W n, pos := (run s n).pos, dir := (run s n).dir }

theorem cacheState_nodup (s : State) (W n : Nat) :
    (cacheState s W n).black.Nodup := (nodup_recentCells s W n).filter _

theorem mem_cacheLive (s : State) (W n : Nat) (p : Point) :
    p ∈ cacheLive s W n ↔ p ∈ recentCells s W n ∧ (run s n).board p = true := by
  simp [cacheLive]

theorem cacheState_read (s : State) (W n : Nat)
    (hm : cacheMissBit s W n = false) :
    (cacheState s W n).toState.board (run s n).pos = readColor s n := by
  apply Bool.eq_iff_iff.mpr
  simp only [cacheState, FiniteState.toState, decide_eq_true_eq, mem_cacheLive,
    readColor]
  constructor
  · exact And.right
  · intro hb
    have hr : (run s n).pos ∈ recentCells s W n := by
      simpa [cacheMissBit, readColor, hb] using hm
    exact ⟨hr, hb⟩

/-- With neither a miss nor a black eviction, the finite cache is a real step. -/
theorem cacheState_step (s : State) {W : Nat} (hW : 0 < W) (n : Nat)
    (hm : cacheMissBit s W n = false) (he : cacheEviction s W n = []) :
    step (cacheState s W n).toState = (cacheState s W (n + 1)).toState := by
  have hc := cacheState_read s W n hm
  have hp := current_mem_recent_next s hW n
  have hb : flip (cacheState s W n).toState.board (run s n).pos =
      (cacheState s W (n + 1)).toState.board := by
    funext q
    by_cases hq : q = (run s n).pos
    · subst q
      rw [flip_same, hc]
      apply Bool.eq_iff_iff.mpr
      change (!readColor s n = true) ↔ decide ((run s n).pos ∈ cacheLive s W (n + 1)) = true
      cases hc0 : (run s n).board (run s n).pos <;>
        simp [mem_cacheLive, hp, run_succ, step, readColor, hc0]
    · have hr : (run s (n + 1)).board q = (run s n).board q := by
        simp [run_succ, step, flip_other, hq]
      simp only [flip_other _ hq, cacheState, FiniteState.toState]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, mem_cacheLive, hr]
      constructor
      · rintro ⟨hqold, hblack⟩
        refine ⟨?_, hblack⟩
        apply Classical.byContradiction
        intro hout
        have hev : q ∈ cacheEviction s W n := by
          apply List.mem_filter.mpr
          exact ⟨List.mem_filter.mpr ⟨hqold, hr.trans hblack⟩, by simp [hout]⟩
        simp [he] at hev
      · rintro ⟨hqnew, hblack⟩
        refine ⟨?_, hblack⟩
        exact (recent_next_subset s W n q hqnew).resolve_left hq
  change State.mk _ (move _ (turn _ _)) (turn _ _) = _
  change State.mk _ (move _ (turn _ _)) (turn _ _) = State.mk _ _ _
  rw [show (cacheState s W n).toState.pos = (run s n).pos from rfl, hc]
  exact congrArg (fun b => State.mk b _ _) hb

theorem cacheState_run (s : State) {W : Nat} (hW : 0 < W) (a k : Nat)
    (hm : ∀ i, i < k -> cacheMissBit s W (a + i) = false)
    (he : ∀ i, i < k -> cacheEviction s W (a + i) = []) :
    run (cacheState s W a).toState k = (cacheState s W (a + k)).toState := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [run_succ, ih (fun i hi => hm i (by omega)) (fun i hi => he i (by omega))]
      exact cacheState_step s hW (a + k) (hm k (by omega)) (he k (by omega))

theorem highwayFrom_translate_return {s : State} {P : Nat} {v : Point}
    (h : run s P = translate v s) : HighwayFrom s 0 P v := by
  intro n _
  have hn : run s (n + P) = translate v (run s n) := by
    rw [Nat.add_comm n P, run_add, h, translate_run]
  rw [hn]
  exact ⟨by simp [translate, addPoint, Int.add_comm], rfl⟩

/-- A whole finite board cannot return to a translate after a positive time. -/
theorem finite_no_translate_return (s : FiniteState) (hs : s.black.Nodup)
    {P : Nat} (hP : 0 < P) (v : Point) :
    run s.toState P ≠ translate v s.toState := by
  intro h
  have hh := highwayFrom_translate_return h
  let bs := s.black.map (addPoint v)
  have hi : Function.Injective (addPoint v) := by
    intro p q hp
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    apply Prod.ext <;> simp only [addPoint] at hx hy ⊢ <;> omega
  have hbs : bs.Nodup := List.Pairwise.map (addPoint v) (fun _ _ hab heq => hab (hi heq)) hs
  have hm : ∀ p, p ∈ bs ↔ (run s.toState (0 + P)).board p = true := by
    intro p
    rw [Nat.zero_add, h]
    simp only [translate, FiniteState.toState, decide_eq_true_eq]
    change p ∈ s.black.map (addPoint v) ↔ subPoint p v ∈ s.black
    constructor
    · rintro hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa only [subPoint_addPoint] using hq
    · intro hp
      exact List.mem_map.mpr ⟨subPoint p v, hp, addPoint_subPoint v p⟩
  have hg := hh.net_black_growth s.finiteSupport hP (Nat.le_refl 0) hs hbs
    (fun p => by simp [FiniteState.toState]) hm
  have hpos := periodic_tail_eight_le_growth s.finiteSupport hP hh
  have hlen : bs.length = s.black.length := List.length_map _
  rw [hlen] at hg
  omega

theorem mem_cacheLive_entry (s : State) {W n : Nat} (hn : W <= n) (p : Point) :
    p ∈ cacheLive s W n ↔ ∃ j, j < W ∧
      (memoryEntry s n j).1 = subPoint p (run s n).pos ∧
      (memoryEntry s n j).2 = true := by
  rw [mem_cacheLive, mem_recentCells]
  constructor
  · rintro ⟨⟨i, hi, hiW, hip⟩, hb⟩
    refine ⟨n - i - 1, by omega, ?_, ?_⟩ <;>
      simp only [memoryEntry, show n - (n - i - 1 + 1) = i from by omega, hip]
    · exact hb
  · rintro ⟨j, hj, hp, hb⟩
    have he : (run s (n - (j + 1))).pos = p := by
      have hx := congrArg Prod.fst hp
      have hy := congrArg Prod.snd hp
      apply Prod.ext <;> simp only [memoryEntry, subPoint] at hx hy ⊢ <;> omega
    refine ⟨⟨n - (j + 1), by omega, by omega, he⟩, ?_⟩
    simpa only [memoryEntry, he] using hb

theorem cacheLive_mem_of_key {s t : State} {W n m : Nat}
    (hn : W <= n) (hm : W <= m) (hk : memoryKey s n W = memoryKey t m W)
    {p q : Point} (hpq : subPoint p (run s n).pos = subPoint q (run t m).pos) :
    p ∈ cacheLive s W n ↔ q ∈ cacheLive t W m := by
  rw [mem_cacheLive_entry s hn, mem_cacheLive_entry t hm]
  constructor
  · rintro ⟨j, hj, hp, hb⟩
    have he := memoryKey_entry hk j hj
    exact ⟨j, hj, (congrArg Prod.fst he).symm.trans (hp.trans hpq),
      (congrArg Prod.snd he).symm.trans hb⟩
  · rintro ⟨j, hj, hp, hb⟩
    have he := memoryKey_entry hk j hj
    exact ⟨j, hj, (congrArg Prod.fst he).trans (hp.trans hpq.symm),
      (congrArg Prod.snd he).trans hb⟩

theorem cacheState_translate_of_key {s t : State} {W n m : Nat}
    (hn : W <= n) (hm : W <= m) (hk : memoryKey s n W = memoryKey t m W) :
    (cacheState t W m).toState =
      translate (subPoint (run t m).pos (run s n).pos) (cacheState s W n).toState := by
  have hd := congrArg Prod.fst hk
  have hb : (cacheState t W m).toState.board =
      (translate (subPoint (run t m).pos (run s n).pos) (cacheState s W n).toState).board := by
    funext p
    apply Bool.eq_iff_iff.mpr
    change decide (p ∈ cacheLive t W m) = true ↔
      decide (subPoint p (subPoint (run t m).pos (run s n).pos) ∈ cacheLive s W n) = true
    simp only [decide_eq_true_eq]
    apply (cacheLive_mem_of_key hn hm hk ?_).symm
    apply Prod.ext <;> simp only [subPoint] <;> omega
  have hp : addPoint (subPoint (run t m).pos (run s n).pos) (run s n).pos =
      (run t m).pos := by
    apply Prod.ext <;> simp only [addPoint, subPoint] <;> omega
  change State.mk _ _ _ = State.mk _ _ _
  simp only [cacheState, FiniteState.toState, hp]
  exact congrArg (fun b => State.mk b _ _) hb |>.trans (by
    rw [show (run t m).dir = (run s n).dir from hd.symm]
    rfl)

/-- An event-free segment cannot repeat a full memory key. No hypothesis on the
initial board's support is needed: only the auxiliary cache is made finite. -/
theorem event_free_key_ne (s : State) {W a k : Nat} (hW : 0 < W) (ha : W <= a)
    (hk : 0 < k)
    (hm : ∀ i, i < k -> cacheMissBit s W (a + i) = false)
    (he : ∀ i, i < k -> cacheEviction s W (a + i) = []) :
    memoryKey s a W ≠ memoryKey s (a + k) W := by
  intro hkey
  have hr := cacheState_run s hW a k hm he
  have ht := cacheState_translate_of_key ha (by omega) hkey
  exact finite_no_translate_return (cacheState s W a) (cacheState_nodup s W a) hk _
    (hr.trans ht)

def keyStateCount (W : Nat) : Nat := (memoryKeys W).length

theorem length_flatMap_uniform {α β : Type} (xs : List α) (f : α -> List β)
    (k : Nat) (h : ∀ x, (f x).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [h, ih, Nat.succ_mul, Nat.add_comm]

theorem memoryWords_length {α : Type} (xs : List α) (n : Nat) :
    (memoryWords xs n).length = xs.length ^ n := by
  induction n with
  | zero => simp [memoryWords]
  | succ n ih =>
      simp only [memoryWords]
      rw [length_flatMap_uniform xs _ (xs.length ^ n) (fun _ => by simp [ih])]
      simp [Nat.pow_succ, Nat.mul_comm]

theorem memoryAlphabet_length (W : Nat) :
    (memoryAlphabet W).length = (2 * W + 1) * ((2 * W + 1) * 2) := by
  unfold memoryAlphabet
  rw [length_flatMap_uniform _ _ ((memoryCoordinates W).length * 2) (fun _ => by
    exact length_flatMap_uniform _ _ 2 (fun _ => rfl))]
  simp [memoryCoordinates]

/-- Size of the explicit full-key universe. This is an upper bound on realizable
keys, not the minimal number of states of a rotation-normalized predictor. -/
theorem keyStateCount_eq (W : Nat) :
    keyStateCount W = 4 * ((2 * W + 1) * ((2 * W + 1) * 2)) ^ W := by
  unfold keyStateCount memoryKeys
  rw [length_flatMap_uniform _ _ ((memoryWords (memoryAlphabet W) W).length)
    (fun _ => List.length_map _)]
  simp only [List.length_cons, List.length_nil, memoryWords_length, memoryAlphabet_length]

/-- The Boolean word universe really has `2^W` entries. Relating it to normalized
cache dynamics is a separate obligation, not a consequence of this count. -/
theorem boolean_suffix_universe_length (W : Nat) :
    (memoryWords [false, true] W).length = 2 ^ W := by
  simpa using memoryWords_length [false, true] W

theorem keyStateCount_pos (W : Nat) : 0 < keyStateCount W := by
  have hm := memoryKey_mem blank (Nat.le_refl W)
  have hp := List.length_pos_of_mem hm
  exact hp

theorem event_in_key_block (s : State) {W a : Nat} (hW : 0 < W) (ha : W <= a) :
    ∃ i, i < keyStateCount W ∧
      (cacheMissBit s W (a + i) = true ∨ cacheEviction s W (a + i) ≠ []) := by
  apply Classical.byContradiction
  intro hnone
  have hm : ∀ i, i < keyStateCount W -> cacheMissBit s W (a + i) = false := by
    intro i hi
    cases hb : cacheMissBit s W (a + i) with
    | false => rfl
    | true => exact False.elim (hnone ⟨i, hi, Or.inl hb⟩)
  have he : ∀ i, i < keyStateCount W -> cacheEviction s W (a + i) = [] := by
    intro i hi
    apply Classical.byContradiction
    exact fun h => hnone ⟨i, hi, Or.inr h⟩
  let ks := (List.range (keyStateCount W + 1)).map (fun i => memoryKey s (a + i) W)
  have hnd : ks.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := List.nodup_range (n := keyStateCount W + 1))
    intro i j hi hj hij heq
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    have hordered : ∀ u v, u < v -> v <= keyStateCount W ->
        memoryKey s (a + u) W ≠ memoryKey s (a + v) W := by
      intro u v huv hv
      have hz : a + u + (v - u) = a + v := by omega
      have hf := event_free_key_ne s hW (a := a + u) (k := v - u) (by omega) (by omega)
        (fun k hk => by simpa [Nat.add_assoc] using hm (u + k) (by omega))
        (fun k hk => by simpa [Nat.add_assoc] using he (u + k) (by omega))
      simpa only [hz] using hf
    by_cases hlt : i < j
    · exact hordered i j hlt (by omega) heq
    · exact hordered j i (by omega) (by omega) heq.symm
  have hsub : ks ⊆ memoryKeys W := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
    exact memoryKey_mem s (by omega)
  have hlen := hnd.length_le_of_subset hsub
  simp only [ks, List.length_map, List.length_range] at hlen
  change keyStateCount W + 1 <= keyStateCount W at hlen
  omega

def eventMass (s : State) (W n : Nat) : Int :=
  bitInt (cacheMissBit s W n) + ((cacheEviction s W n).length : Int)

theorem eventMass_nonneg (s : State) (W n : Nat) : 0 <= eventMass s W n := by
  unfold eventMass bitInt
  split <;> omega

theorem sumFrom_nonneg {f : Nat -> Int} (hf : ∀ n, 0 <= f n) (a n : Nat) :
    0 <= sumFrom f a n := by
  induction n with
  | zero => simp [sumFrom]
  | succ n ih => have h := hf (a + n); simp only [sumFrom]; omega

theorem term_le_sumFrom {f : Nat -> Int} (hf : ∀ n, 0 <= f n)
    {a n i : Nat} (hi : i < n) : f (a + i) <= sumFrom f a n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hn := hf (a + n)
      have hs := sumFrom_nonneg hf a n
      simp only [sumFrom]
      by_cases he : i = n
      · subst i; omega
      · have h := ih (by omega); omega

theorem key_block_mass (s : State) {W a : Nat} (hW : 0 < W) (ha : W <= a) :
    1 <= sumFrom (eventMass s W) a (keyStateCount W) := by
  obtain ⟨i, hi, he⟩ := event_in_key_block s hW ha
  have ht := term_le_sumFrom (eventMass_nonneg s W) (a := a) hi
  have hp : 1 <= eventMass s W (a + i) := by
    rcases he with hm | he
    · simp only [eventMass, bitInt, hm, ite_true]; omega
    · have hl : 0 < (cacheEviction s W (a + i)).length := List.length_pos_iff.mpr he
      unfold eventMass bitInt
      split <;> omega
  omega

theorem key_blocks_mass (s : State) {W a : Nat} (hW : 0 < W) (ha : W <= a)
    (q : Nat) : (q : Int) <= sumFrom (eventMass s W) a (q * keyStateCount W) := by
  induction q with
  | zero => simp [sumFrom]
  | succ q ih =>
      have hb := key_block_mass s hW (a := a + q * keyStateCount W) (by omega)
      rw [Nat.succ_mul, sumFrom_add]
      omega

theorem sumFrom_eventMass (s : State) (W a n : Nat) :
    sumFrom (eventMass s W) a n = missCount s W a n + evictionCount s W a n := by
  induction n with
  | zero => simp [sumFrom, missCount, evictionCount]
  | succ n ih =>
      simp only [missCount, evictionCount, sumFrom, eventMass] at ih ⊢
      omega

/-- An unconditional event bound with the existing full-key universe, not `2^W`. -/
theorem event_bound_full_key (s : State) {W a : Nat} (hW : 0 < W) (ha : W <= a)
    (n : Nat) : (n / keyStateCount W : Nat) <=
      missCount s W a n + evictionCount s W a n := by
  have hb := key_blocks_mass s hW ha (n / keyStateCount W)
  have hr := sumFrom_nonneg (eventMass_nonneg s W)
    (a + n / keyStateCount W * keyStateCount W) (n % keyStateCount W)
  have hsplit : n / keyStateCount W * keyStateCount W + n % keyStateCount W = n := by
    have h := Nat.mod_add_div n (keyStateCount W)
    simpa only [Nat.mul_comm, Nat.add_comm] using h
  have ht := sumFrom_add (eventMass s W) a
    (n / keyStateCount W * keyStateCount W) (n % keyStateCount W)
  rw [hsplit, sumFrom_eventMass] at ht
  omega

/-- A weaker, separately named C2-type theorem; the sharp paper denominator is
not claimed. All subtractions in the statement are signed integer operations. -/
theorem black_bound_full_key (s : FiniteState) (hnd : s.black.Nodup)
    {W N : Nat} (hW : 0 < W) (hN : W <= N) :
    ((s.run W).black.length : Int) - (W : Int) +
      ((N - W) / keyStateCount W : Nat) - 2 * missCount s.toState W W (N - W) <=
        ((s.run N).black.length : Int) := by
  have h := black_bound_of_event_bound s hnd hW W (N - W)
    ((N - W) / keyStateCount W)
    (event_bound_full_key s.toState hW (Nat.le_refl W) (N - W))
  simpa only [Nat.add_sub_cancel' hN] using h

/-- Growing a window adds the current read and forgets no visited cell. -/
theorem memoryKey_grow {s t : State} {n m W : Nat}
    (h : memoryKey s n W = memoryKey t m W)
    (hc : readColor s n = readColor t m) :
    memoryKey s (n + 1) (W + 1) = memoryKey t (m + 1) (W + 1) := by
  have hd : (run s n).dir = (run t m).dir := congrArg Prod.fst h
  have ht : turn ((run s n).board (run s n).pos) (run s n).dir =
      turn ((run t m).board (run t m).pos) (run t m).dir := by
    change turn (readColor s n) _ = turn (readColor t m) _
    rw [hc, hd]
  apply Prod.ext
  · exact ht
  · apply List.map_congr_left
    intro j hj
    have hjW := List.mem_range.mp hj
    cases j with
    | zero =>
        have hp := relative_move_eq (p := (run s n).pos) (q := (run t m).pos)
          (a := (run s n).pos) (b := (run t m).pos) (by simp [subPoint])
          (turn (readColor t m) (run t m).dir)
        apply Prod.ext
        · simpa only [memoryEntry, Nat.add_sub_cancel, run_succ, step, readColor, ht] using hp
        · simpa only [memoryEntry, Nat.add_sub_cancel, run_succ, step, flip_same, readColor]
            using congrArg Bool.not hc
    | succ j =>
        have he := memoryKey_entry h j (by omega)
        have hp := congrArg Prod.fst he
        have hb := congrArg Prod.snd he
        have hcenter := relative_center_iff hp
        have htime1 : n + 1 - (j + 1 + 1) = n - (j + 1) := by omega
        have htime2 : m + 1 - (j + 1 + 1) = m - (j + 1) := by omega
        apply Prod.ext
        · have hr := relative_move_eq hp (turn (readColor t m) (run t m).dir)
          simpa only [memoryEntry, htime1, htime2, run_succ, step, readColor, ht] using hr
        · change flip (run s n).board (run s n).pos (run s (n + 1 - (j + 1 + 1))).pos =
            flip (run t m).board (run t m).pos (run t (m + 1 - (j + 1 + 1))).pos
          rw [htime1, htime2]
          change (run s n).board (run s (n - (j + 1))).pos =
            (run t m).board (run t (m - (j + 1))).pos at hb
          simp only [flip, hcenter, hb]

theorem memoryKey_of_reads {s t : State} (a b W : Nat)
    (hd : (run s a).dir = (run t b).dir)
    (hc : ∀ i, i < W -> readColor s (a + i) = readColor t (b + i)) :
    memoryKey s (a + W) W = memoryKey t (b + W) W := by
  induction W with
  | zero => simp [memoryKey, hd]
  | succ W ih =>
      exact memoryKey_grow (ih (fun i hi => hc i (by omega))) (hc W (by omega))

def rigid (r : Direction) (v : Point) (s : State) : State :=
  translate v (rotateState r s)

theorem rigid_run (r : Direction) (v : Point) (s : State) (n : Nat) :
    run (rigid r v s) n = rigid r v (run s n) := by
  simp only [rigid, translate_run, rotate_run]

theorem rigid_four (r : Direction) (v : Point) (s : State) :
    rigid r v (rigid r v (rigid r v (rigid r v s))) =
      translate (if r = .north then (4 * v.1, 4 * v.2) else (0, 0)) s := by
  cases s with
  | mk board pos dir =>
    cases r <;> cases dir <;>
      simp [rigid, translate, rotateState, rotatePoint, inverseRotation, rotateDir,
        Direction.right, Direction.left, subPoint, addPoint] <;>
      refine ⟨?_, by omega, by omega⟩
    all_goals
      funext p
      congr 1 <;> apply Prod.ext <;> simp only <;> omega

theorem finite_no_rigid_return (s : FiniteState) (hs : s.black.Nodup)
    {P : Nat} (hP : 0 < P) (r : Direction) (v : Point) :
    run s.toState P ≠ rigid r v s.toState := by
  intro h
  have h2 : run s.toState (P + P) = rigid r v (rigid r v s.toState) := by
    rw [run_add, h, rigid_run, h]
  have h3 : run s.toState (P + P + P) = rigid r v (rigid r v (rigid r v s.toState)) := by
    rw [run_add, h2, rigid_run, rigid_run, h]
  have h4 : run s.toState (P + P + P + P) =
      rigid r v (rigid r v (rigid r v (rigid r v s.toState))) := by
    rw [run_add, h3, rigid_run, rigid_run, rigid_run, h]
  rw [rigid_four] at h4
  exact finite_no_translate_return s hs (by omega) _ h4

theorem rotatePoint_eq_iff (r : Direction) (p q : Point) :
    rotatePoint r p = q ↔ p = rotatePoint (inverseRotation r) q := by
  constructor
  · intro h
    simpa only [rotatePoint_inverse] using congrArg (rotatePoint (inverseRotation r)) h
  · intro h
    rw [h, inverse_rotatePoint]

theorem cacheState_rotate (s : State) (W n : Nat) (r : Direction) :
    (cacheState (rotateState r s) W n).toState = rotateState r (cacheState s W n).toState := by
  have hm : ∀ p, p ∈ cacheLive (rotateState r s) W n ↔
      rotatePoint (inverseRotation r) p ∈ cacheLive s W n := by
    intro p
    simp only [mem_cacheLive, mem_recentCells]
    simp only [rotate_run]
    simp only [rotateState, rotatePoint_eq_iff]
  have hb : (cacheState (rotateState r s) W n).toState.board =
      (rotateState r (cacheState s W n).toState).board := by
    funext p
    apply Bool.eq_iff_iff.mpr
    change decide (p ∈ cacheLive (rotateState r s) W n) = true ↔
      decide (rotatePoint (inverseRotation r) p ∈ cacheLive s W n) = true
    simpa only [decide_eq_true_eq] using hm p
  change State.mk _ _ _ = State.mk _ _ _
  simp only [cacheState, FiniteState.toState, rotate_run]
  exact congrArg (fun b => State.mk b _ _) hb

def readSuffix (s : State) (W n : Nat) : List Bool :=
  (List.range W).map (fun i => readColor s (n - W + i))

theorem readSuffix_entry {s t : State} {W n m : Nat}
    (h : readSuffix s W n = readSuffix t W m) (i : Nat) (hi : i < W) :
    readColor s (n - W + i) = readColor t (m - W + i) := by
  have he := congrArg (fun xs => xs[i]?) h
  simpa only [readSuffix, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] using he

theorem readSuffix_mem (s : State) (W n : Nat) :
    readSuffix s W n ∈ memoryWords [false, true] W := by
  have h := mem_memoryWords [false, true] (readSuffix s W n) (by
    intro b _
    cases b <;> simp)
  simpa only [readSuffix, List.length_map, List.length_range] using h

/-- The last W reads determine the entire cached state up to a rigid motion.
No assumption about misses, evictions, or earlier board colors is needed. -/
theorem cacheState_rigid_of_suffix {s t : State} {W n m : Nat}
    (hn : W <= n) (hm : W <= m) (hc : readSuffix s W n = readSuffix t W m) :
    ∃ r v, (cacheState t W m).toState = rigid r v (cacheState s W n).toState := by
  have hdr : ∃ r, rotateDir r (run s (n - W)).dir = (run t (m - W)).dir := by
    cases (run s (n - W)).dir <;> cases (run t (m - W)).dir <;>
      first | exact ⟨.north, rfl⟩ | exact ⟨.east, rfl⟩ |
        exact ⟨.south, rfl⟩ | exact ⟨.west, rfl⟩
  obtain ⟨r, hr⟩ := hdr
  have hd : (run (rotateState r s) (n - W)).dir = (run t (m - W)).dir := by
    rw [rotate_run]
    exact hr
  have hh := memoryKey_of_reads (s := rotateState r s) (t := t) (n - W) (m - W) W hd
    (fun i hi => by rw [rotate_readColor]; exact readSuffix_entry hc i hi)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hm] at hh
  have ht := cacheState_translate_of_key hn hm hh
  rw [cacheState_rotate] at ht
  exact ⟨r, _, ht⟩

theorem finite_card_eq_of_rigid (s t : FiniteState)
    (hs : s.black.Nodup) (ht : t.black.Nodup) (r : Direction) (v : Point)
    (he : t.toState = rigid r v s.toState) : s.black.length = t.black.length := by
  let f := fun p => addPoint v (rotatePoint r p)
  let g := fun p => rotatePoint (inverseRotation r) (subPoint p v)
  have hgf : ∀ p, g (f p) = p := by
    intro p
    simp only [g, f, subPoint_addPoint, rotatePoint_inverse]
  have hfg : ∀ p, f (g p) = p := by
    intro p
    simp only [g, f, inverse_rotatePoint, addPoint_subPoint]
  have hi : Function.Injective f := by
    intro p q hpq
    simpa only [hgf] using congrArg g hpq
  have hnd : (s.black.map f).Nodup :=
    List.Pairwise.map f (fun _ _ hab heq => hab (hi heq)) hs
  have hperm : (s.black.map f).Perm t.black := by
    apply (List.perm_ext_iff_of_nodup hnd ht).mpr
    intro p
    have hb : p ∈ t.black ↔ g p ∈ s.black := by
      have h := congrArg (fun st : State => st.board p = true) he
      change (decide (p ∈ t.black) = true) = (decide (g p ∈ s.black) = true) at h
      simpa only [decide_eq_true_eq] using h.to_iff
    rw [hb]
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa only [hgf] using hq
    · intro hp
      exact List.mem_map.mpr ⟨g p, hp, hfg p⟩
  simpa only [List.length_map] using hperm.length_eq

/-- In particular, suffix equality preserves cache cardinality even when the
absolute headings or positions differ. -/
theorem cacheLive_length_eq_of_suffix {s t : State} {W n m : Nat}
    (hn : W <= n) (hm : W <= m) (hc : readSuffix s W n = readSuffix t W m) :
    (cacheLive s W n).length = (cacheLive t W m).length := by
  obtain ⟨r, v, he⟩ := cacheState_rigid_of_suffix hn hm hc
  exact finite_card_eq_of_rigid (cacheState s W n) (cacheState t W m)
    (cacheState_nodup s W n) (cacheState_nodup t W m) r v he

theorem event_free_suffix_ne (s : State) {W a k : Nat} (hW : 0 < W) (ha : W <= a)
    (hk : 0 < k)
    (hm : ∀ i, i < k -> cacheMissBit s W (a + i) = false)
    (he : ∀ i, i < k -> cacheEviction s W (a + i) = []) :
    readSuffix s W a ≠ readSuffix s W (a + k) := by
  intro hc
  obtain ⟨r, v, hr⟩ := cacheState_rigid_of_suffix ha (by omega) hc
  exact finite_no_rigid_return (cacheState s W a) (cacheState_nodup s W a) hk r v
    ((cacheState_run s hW a k hm he).trans hr)

/-- The sharp pigeonhole block uses Boolean suffixes, not full memory keys. -/
theorem event_in_suffix_block (s : State) {W a : Nat} (hW : 0 < W) (ha : W <= a) :
    ∃ i, i < 2 ^ W ∧
      (cacheMissBit s W (a + i) = true ∨ cacheEviction s W (a + i) ≠ []) := by
  apply Classical.byContradiction
  intro hnone
  have hm : ∀ i, i < 2 ^ W -> cacheMissBit s W (a + i) = false := by
    intro i hi
    cases hb : cacheMissBit s W (a + i) with
    | false => rfl
    | true => exact False.elim (hnone ⟨i, hi, Or.inl hb⟩)
  have he : ∀ i, i < 2 ^ W -> cacheEviction s W (a + i) = [] := by
    intro i hi
    apply Classical.byContradiction
    exact fun h => hnone ⟨i, hi, Or.inr h⟩
  let ks := (List.range (2 ^ W + 1)).map (fun i => readSuffix s W (a + i))
  have hnd : ks.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := List.nodup_range (n := 2 ^ W + 1))
    intro i j hi hj hij heq
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    have hordered : ∀ u v, u < v -> v <= 2 ^ W ->
        readSuffix s W (a + u) ≠ readSuffix s W (a + v) := by
      intro u v huv hv
      have hz : a + u + (v - u) = a + v := by omega
      have hf := event_free_suffix_ne s hW (a := a + u) (k := v - u) (by omega) (by omega)
        (fun k hk => by simpa [Nat.add_assoc] using hm (u + k) (by omega))
        (fun k hk => by simpa [Nat.add_assoc] using he (u + k) (by omega))
      simpa only [hz] using hf
    by_cases hlt : i < j
    · exact hordered i j hlt (by omega) heq
    · exact hordered j i (by omega) (by omega) heq.symm
  have hsub : ks ⊆ memoryWords [false, true] W := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
    exact readSuffix_mem s W (a + i)
  have hlen := hnd.length_le_of_subset hsub
  simp only [ks, List.length_map, List.length_range, boolean_suffix_universe_length] at hlen
  omega

theorem suffix_block_mass (s : State) {W a : Nat} (hW : 0 < W) (ha : W <= a) :
    1 <= sumFrom (eventMass s W) a (2 ^ W) := by
  obtain ⟨i, hi, he⟩ := event_in_suffix_block s hW ha
  have ht := term_le_sumFrom (eventMass_nonneg s W) (a := a) hi
  have hp : 1 <= eventMass s W (a + i) := by
    rcases he with hm | he
    · simp only [eventMass, bitInt, hm, ite_true]; omega
    · have hl : 0 < (cacheEviction s W (a + i)).length := List.length_pos_iff.mpr he
      unfold eventMass bitInt
      split <;> omega
  omega

theorem suffix_blocks_mass (s : State) {W a : Nat} (hW : 0 < W) (ha : W <= a)
    (q : Nat) : (q : Int) <= sumFrom (eventMass s W) a (q * 2 ^ W) := by
  induction q with
  | zero => simp [sumFrom]
  | succ q ih =>
      have hb := suffix_block_mass s hW (a := a + q * 2 ^ W) (by omega)
      rw [Nat.succ_mul, sumFrom_add]
      omega

/-- Unconditional sharp event bound, even for an infinite-support original board. -/
theorem event_bound_suffix (s : State) {W a : Nat} (hW : 0 < W) (ha : W <= a)
    (n : Nat) : (n / 2 ^ W : Nat) <=
      missCount s W a n + evictionCount s W a n := by
  have hb := suffix_blocks_mass s hW ha (n / 2 ^ W)
  have hr := sumFrom_nonneg (eventMass_nonneg s W)
    (a + n / 2 ^ W * 2 ^ W) (n % 2 ^ W)
  have hsplit : n / 2 ^ W * 2 ^ W + n % 2 ^ W = n := by
    simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n (2 ^ W)
  have ht := sumFrom_add (eventMass s W) a (n / 2 ^ W * 2 ^ W) (n % 2 ^ W)
  rw [hsplit, sumFrom_eventMass] at ht
  omega

/-- C2 with its original `2^W` denominator and no predictor premise. -/
theorem black_bound_suffix (s : FiniteState) (hnd : s.black.Nodup)
    {W N : Nat} (hW : 0 < W) (hN : W <= N) :
    ((s.run W).black.length : Int) - (W : Int) +
      ((N - W) / 2 ^ W : Nat) - 2 * missCount s.toState W W (N - W) <=
        ((s.run N).black.length : Int) := by
  have h := black_bound_of_event_bound s hnd hW W (N - W)
    ((N - W) / 2 ^ W)
    (event_bound_suffix s.toState hW (Nat.le_refl W) (N - W))
  simpa only [Nat.add_sub_cancel' hN] using h

/-- Every finite-support board has a duplicate-free exact finite representation. -/
theorem finiteSupport_representation (s : State) (hs : FiniteSupport s.board) :
    ∃ fs : FiniteState, fs.black.Nodup ∧ fs.toState = s := by
  obtain ⟨xs, hx⟩ := hs
  let bs := (unique xs).filter s.board
  have hb : ∀ p, p ∈ bs ↔ s.board p = true := by
    intro p
    simp only [bs, List.mem_filter, mem_unique]
    exact ⟨And.right, fun hp => ⟨hx p hp, hp⟩⟩
  refine ⟨⟨bs, s.pos, s.dir⟩, (nodup_unique xs).filter _, ?_⟩
  have he : (fun p => decide (p ∈ bs)) = s.board := by
    funext p
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hb p
  cases s
  simp only [FiniteState.toState, he]

theorem finite_run_card_eq (fs : FiniteState) (hfs : fs.black.Nodup) (n : Nat)
    (bs : List Point) (hbs : bs.Nodup)
    (hb : ∀ p, p ∈ bs ↔ (run fs.toState n).board p = true) :
    (fs.run n).black.length = bs.length := by
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup (fs.nodup_run hfs n) hbs).mpr
  intro p
  rw [hb p, ← fs.toState_run]
  simp [FiniteState.toState]

/-- Representation-independent C2: `BW` and `BN` enumerate the exact black sets
without duplicates. The initial state is an arbitrary finite-support `State`. -/
theorem black_bound_finiteSupport (s : State) (hs : FiniteSupport s.board)
    {W N : Nat} (hW : 0 < W) (hN : W <= N)
    (BW BN : List Point) (hBW : BW.Nodup) (hBN : BN.Nodup)
    (hBWexact : ∀ p, p ∈ BW ↔ (run s W).board p = true)
    (hBNexact : ∀ p, p ∈ BN ↔ (run s N).board p = true) :
    (BW.length : Int) - (W : Int) + ((N - W) / 2 ^ W : Nat) -
      2 * missCount s W W (N - W) <= (BN.length : Int) := by
  obtain ⟨fs, hfs, he⟩ := finiteSupport_representation s hs
  have h := black_bound_suffix fs hfs hW hN
  have hw := finite_run_card_eq fs hfs W BW hBW (by simpa only [he] using hBWexact)
  have hn := finite_run_card_eq fs hfs N BN hBN (by simpa only [he] using hBNexact)
  simpa only [hw, hn, he] using h

end LangtonsAnt.BlackCountBound
