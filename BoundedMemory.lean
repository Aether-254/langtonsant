import SingleFlipReduction

namespace LangtonsAnt

/-- Every read is either a recent revisit or the first visit to an initially white cell. -/
def BoundedMemoryFrom (s : State) (T W : Nat) : Prop :=
  forall n, T <= n ->
    (exists j, j < n ∧ n <= j + W ∧ (run s j).pos = (run s n).pos) ∨
    ((forall j, j < n -> (run s j).pos ≠ (run s n).pos) ∧ s.board (run s n).pos = false)

def EventuallyBoundedMemory (s : State) : Prop := exists T W, BoundedMemoryFrom s T W

def memoryEntry (s : State) (n j : Nat) : Point × Bool :=
  (subPoint (run s (n - (j + 1))).pos (run s n).pos,
    (run s n).board (run s (n - (j + 1))).pos)

def memoryKey (s : State) (n W : Nat) : Direction × List (Point × Bool) :=
  ((run s n).dir, (List.range W).map (memoryEntry s n))

theorem memoryKey_entry {s t : State} {n m W : Nat} (h : memoryKey s n W = memoryKey t m W)
    (j : Nat) (hj : j < W) : memoryEntry s n j = memoryEntry t m j := by
  have he := congrArg (fun k : Direction × List (Point × Bool) => k.2[j]?) h
  simpa only [memoryKey, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.some.injEq] using he

theorem memoryKey_reads_of_recent {s t : State} {n m W : Nat}
    (h : memoryKey s n W = memoryKey t m W)
    (hr : exists j, j < n ∧ n <= j + W ∧ (run s j).pos = (run s n).pos) :
    readColor s n = readColor t m := by
  obtain ⟨j, hj, hW, hp⟩ := hr
  have he := memoryKey_entry h (n - j - 1) (by omega)
  have htime : n - (n - j - 1 + 1) = j := by omega
  simp only [memoryEntry, htime, hp] at he
  have hx := congrArg (fun a : Point × Bool => a.1.1) he
  have hy := congrArg (fun a : Point × Bool => a.1.2) he
  have hc := congrArg Prod.snd he
  have ht : (run t (m - (n - j - 1 + 1))).pos = (run t m).pos := by
    apply Prod.ext <;> simp only [subPoint] at hx hy ⊢ <;> omega
  simpa only [ht, readColor] using hc

theorem memoryKey_reads {s t : State} {T U W n m : Nat}
    (hs : BoundedMemoryFrom s T W) (ht : BoundedMemoryFrom t U W)
    (hn : T <= n) (hm : U <= m) (h : memoryKey s n W = memoryKey t m W) :
    readColor s n = readColor t m := by
  rcases hs n hn with hr | hf
  · exact memoryKey_reads_of_recent h hr
  · rcases ht m hm with hr | hg
    · exact (memoryKey_reads_of_recent h.symm hr).symm
    · have hc := board_unchanged_of_avoids s (run s n).pos n hf.1
      have hd := board_unchanged_of_avoids t (run t m).pos m hg.1
      exact (hc.trans hf.2).trans (hd.trans hg.2).symm

theorem subPoint_eq_zero_iff (p q : Point) : subPoint p q = (0, 0) ↔ p = q := by
  constructor
  · intro h
    apply Prod.ext <;> simp only [subPoint, Prod.mk.injEq] at h ⊢ <;> omega
  · rintro rfl
    simp [subPoint]

theorem relative_move_eq {p q a b : Point} (h : subPoint p a = subPoint q b) (d : Direction) :
    subPoint p (move a d) = subPoint q (move b d) := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  cases d <;> apply Prod.ext <;> simp only [subPoint, move] at hx hy ⊢ <;> omega

theorem relative_center_iff {p q a b : Point} (h : subPoint p a = subPoint q b) : p = a ↔ q = b := by
  exact (subPoint_eq_zero_iff p a).symm.trans ((congrArg (fun x => x = (0, 0)) h).to_iff.trans
    (subPoint_eq_zero_iff q b))

theorem memoryKey_step {s t : State} {n m W : Nat}
    (hn : W <= n) (hm : W <= m) (h : memoryKey s n W = memoryKey t m W)
    (hc : readColor s n = readColor t m) : memoryKey s (n + 1) W = memoryKey t (m + 1) W := by
  have hd : (run s n).dir = (run t m).dir := congrArg Prod.fst h
  have hturn : turn (readColor s n) (run s n).dir = turn (readColor t m) (run t m).dir := by rw [hc, hd]
  have hc' : (run s n).board (run s n).pos = (run t m).board (run t m).pos := hc
  have hturn' : turn ((run s n).board (run s n).pos) (run s n).dir =
      turn ((run t m).board (run t m).pos) (run t m).dir := hturn
  apply Prod.ext
  · exact hturn
  · apply List.map_congr_left
    intro j hj
    have hjW : j < W := List.mem_range.mp hj
    cases j with
    | zero =>
      have hrel : subPoint (run s n).pos (run s n).pos = subPoint (run t m).pos (run t m).pos := by
        simp [subPoint]
      have hp := relative_move_eq hrel (turn (readColor t m) (run t m).dir)
      apply Prod.ext
      · simpa only [memoryEntry, Nat.add_sub_cancel, run_succ, step, readColor, hturn'] using hp
      · simp only [memoryEntry, Nat.add_sub_cancel, run_succ, step, flip_same, hc']
    | succ j =>
      have he := memoryKey_entry h j (by omega)
      have hp := congrArg Prod.fst he
      have hb := congrArg Prod.snd he
      change (run s n).board (run s (n - (j + 1))).pos = (run t m).board (run t (m - (j + 1))).pos at hb
      have ht1 : n + 1 - (j + 1 + 1) = n - (j + 1) := by omega
      have ht2 : m + 1 - (j + 1 + 1) = m - (j + 1) := by omega
      have hcenter := relative_center_iff hp
      apply Prod.ext
      · have hr := relative_move_eq hp (turn (readColor t m) (run t m).dir)
        simpa only [memoryEntry, ht1, ht2, run_succ, step, readColor, hturn'] using hr
      · change flip (run s n).board (run s n).pos (run s (n + 1 - (j + 1 + 1))).pos =
          flip (run t m).board (run t m).pos (run t (m + 1 - (j + 1 + 1))).pos
        rw [ht1, ht2]
        simp only [flip, hcenter, hb]

theorem memoryKey_future {s : State} {T W n m : Nat} (hs : BoundedMemoryFrom s T W)
    (hn : T <= n) (hm : T <= m) (hnW : W <= n) (hmW : W <= m)
    (h : memoryKey s n W = memoryKey s m W) (k : Nat) :
    memoryKey s (n + k) W = memoryKey s (m + k) W := by
  induction k with
  | zero => simpa only [Nat.add_zero] using h
  | succ k ih =>
    exact memoryKey_step (n := n + k) (m := m + k) (by omega) (by omega) ih
      (memoryKey_reads (n := n + k) (m := m + k) hs hs (by omega) (by omega) ih)

theorem run_displacement_bounds (s : State) (k : Nat) :
    s.pos.1 - (k : Int) <= (run s k).pos.1 ∧
    (run s k).pos.1 <= s.pos.1 + (k : Int) ∧
    s.pos.2 - (k : Int) <= (run s k).pos.2 ∧
    (run s k).pos.2 <= s.pos.2 + (k : Int) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [run_succ, step]
    cases turn ((run s k).board (run s k).pos) (run s k).dir <;>
      simp only [move, Int.natCast_add, Int.natCast_one] <;> omega

def memoryCoordinates (W : Nat) : List Int :=
  (List.range (2 * W + 1)).map (fun (i : Nat) => (i : Int) - (W : Int))

theorem mem_memoryCoordinates {W : Nat} {x : Int}
    (hlo : -(W : Int) <= x) (hhi : x <= (W : Int)) : x ∈ memoryCoordinates W := by
  apply List.mem_map.mpr
  refine ⟨(x + (W : Int)).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

def memoryAlphabet (W : Nat) : List (Point × Bool) :=
  (memoryCoordinates W).flatMap fun x =>
    (memoryCoordinates W).flatMap fun y => [((x, y), false), ((x, y), true)]

theorem memoryEntry_mem (s : State) {n W j : Nat} (hn : W <= n) (hj : j < W) :
    memoryEntry s n j ∈ memoryAlphabet W := by
  have htime : n - (j + 1) + (j + 1) = n := by omega
  have hb := run_displacement_bounds (run s (n - (j + 1))) (j + 1)
  rw [← run_add, htime] at hb
  have hx : (memoryEntry s n j).1.1 ∈ memoryCoordinates W := by
    apply mem_memoryCoordinates <;> simp only [memoryEntry, subPoint] <;> omega
  have hy : (memoryEntry s n j).1.2 ∈ memoryCoordinates W := by
    apply mem_memoryCoordinates <;> simp only [memoryEntry, subPoint] <;> omega
  apply List.mem_flatMap.mpr
  refine ⟨_, hx, List.mem_flatMap.mpr ⟨_, hy, ?_⟩⟩
  have he : memoryEntry s n j =
      (((memoryEntry s n j).1.1, (memoryEntry s n j).1.2), (memoryEntry s n j).2) := rfl
  cases hc : (memoryEntry s n j).2 <;> simp only [List.mem_cons, List.not_mem_nil, or_false]
  · exact Or.inl (he.trans (by rw [hc]))
  · exact Or.inr (he.trans (by rw [hc]))

def memoryWords {α : Type} (alphabet : List α) : Nat -> List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (memoryWords alphabet n).map (a :: ·)

theorem mem_memoryWords {α : Type} (alphabet : List α) (xs : List α)
    (h : forall x, x ∈ xs -> x ∈ alphabet) : xs ∈ memoryWords alphabet xs.length := by
  induction xs with
  | nil => simp [memoryWords]
  | cons x xs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨x, h x (by simp), List.mem_map.mpr ⟨xs, ?_, rfl⟩⟩
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

def memoryKeys (W : Nat) : List (Direction × List (Point × Bool)) :=
  [Direction.north, .east, .south, .west].flatMap fun d =>
    (memoryWords (memoryAlphabet W) W).map (d, ·)

/-- An explicit finite universe for every window after its full width is available. -/
theorem memoryKey_mem (s : State) {n W : Nat} (hn : W <= n) :
    memoryKey s n W ∈ memoryKeys W := by
  have hwords := mem_memoryWords (memoryAlphabet W) ((List.range W).map (memoryEntry s n)) (by
    intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    exact memoryEntry_mem s hn (List.mem_range.mp hj))
  simp only [List.length_map, List.length_range] at hwords
  apply List.mem_flatMap.mpr
  refine ⟨(run s n).dir, ?_, List.mem_map.mpr ⟨_, hwords, rfl⟩⟩
  cases (run s n).dir <;> simp

/-- Infinite pigeonhole principle for an explicitly listed range. -/
theorem finite_list_repeats {α : Type} (xs : List α) (f : Nat -> α)
    (h : forall n, f n ∈ xs) : exists n m, n < m ∧ f n = f m := by
  classical
  induction xs generalizing f with
  | nil => simpa using h 0
  | cons a xs ih =>
    by_cases ha : exists n, f n = a
    · obtain ⟨n, hn⟩ := ha
      by_cases hb : exists m, n < m ∧ f m = a
      · obtain ⟨m, hm, he⟩ := hb
        exact ⟨n, m, hm, hn.trans he.symm⟩
      · have htail : forall k, f (n + 1 + k) ∈ xs := by
          intro k
          rcases List.mem_cons.mp (h (n + 1 + k)) with he | he
          · exact False.elim (hb ⟨n + 1 + k, by omega, he⟩)
          · exact he
        obtain ⟨i, j, hij, he⟩ := ih (fun k => f (n + 1 + k)) htail
        exact ⟨n + 1 + i, n + 1 + j, by omega, he⟩
    · apply ih f
      intro n
      rcases List.mem_cons.mp (h n) with he | he
      · exact False.elim (ha ⟨n, he⟩)
      · exact he

theorem memoryKey_repeats (s : State) (T W : Nat) :
    exists n m, T <= n ∧ W <= n ∧ n < m ∧ memoryKey s n W = memoryKey s m W := by
  obtain ⟨i, j, hij, he⟩ := finite_list_repeats (memoryKeys W)
    (fun k => memoryKey s (T + W + k) W) (fun k => memoryKey_mem s (by omega))
  exact ⟨T + W + i, T + W + j, by omega, by omega, by omega, he⟩

theorem memoryKey_future_positions {s : State} {T W n m : Nat}
    (hs : BoundedMemoryFrom s T W) (hn : T <= n) (hm : T <= m)
    (hnW : W <= n) (hmW : W <= m) (h : memoryKey s n W = memoryKey s m W) (k : Nat) :
    (run s (m + k)).pos =
      addPoint (subPoint (run s m).pos (run s n).pos) (run s (n + k)).pos := by
  induction k with
  | zero => apply Prod.ext <;> simp [addPoint, subPoint] <;> omega
  | succ k ih =>
    have hk := memoryKey_future hs hn hm hnW hmW h k
    have hd : (run s (n + k)).dir = (run s (m + k)).dir := congrArg Prod.fst hk
    have hc := memoryKey_reads hs hs (n := n + k) (m := m + k) (by omega) (by omega) hk
    simp only [Nat.add_succ, run_succ, step]
    change move (run s (m + k)).pos (turn (readColor s (m + k)) (run s (m + k)).dir) = _
    rw [← hc, ← hd, ih, move_addPoint]
    rfl

theorem highwayFrom_of_memoryKey_eq {s : State} {T W n m : Nat}
    (hs : BoundedMemoryFrom s T W) (hn : T <= n) (hnW : W <= n) (hnm : n < m)
    (h : memoryKey s n W = memoryKey s m W) :
    HighwayFrom s n (m - n) (subPoint (run s m).pos (run s n).pos) := by
  intro t ht
  have hp := memoryKey_future_positions hs hn (by omega) hnW (by omega) h (t - n)
  have hd := congrArg Prod.fst (memoryKey_future hs hn (by omega) hnW (by omega) h (t - n))
  have ht1 : n + (t - n) = t := by omega
  have ht2 : m + (t - n) = t + (m - n) := by omega
  rw [ht1, ht2] at hp hd
  refine ⟨?_, hd.symm⟩
  simpa only [addPoint, Int.add_comm] using hp

/-- Zero drift would trap the entire tail in the finite set of one period's positions. -/
theorem HighwayFrom.drift_ne_zero {s : State} {T P : Nat} {v : Point}
    (h : HighwayFrom s T P v) (hP : 0 < P) : v ≠ (0, 0) := by
  intro hv
  subst v
  have hp : forall k j, (run s (T + P * k + j)).pos = (run s (T + j)).pos := by
    intro k j
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := (h (T + P * k + j) (by omega)).1
      have he : T + P * (k + 1) + j = T + P * k + j + P := by rw [Nat.mul_succ]; omega
      rw [he, hh]
      simpa using ih
  let cells := (List.range P).map (fun j => (run s (T + j)).pos)
  obtain ⟨n, hn, hnot⟩ := escapes_finite_set_after s cells T
  apply hnot
  have he : T + P * ((n - T) / P) + (n - T) % P = n := by
    have := Nat.div_add_mod (n - T) P
    omega
  have hpos := hp ((n - T) / P) ((n - T) % P)
  rw [he] at hpos
  exact List.mem_map.mpr ⟨(n - T) % P, List.mem_range.mpr (Nat.mod_lt _ hP), hpos.symm⟩

/-- L1 uses the strong fresh-white condition and needs no finite-support hypothesis. -/
theorem BoundedMemoryFrom.highway {s : State} {T W : Nat} (h : BoundedMemoryFrom s T W) :
    exists U P v, T <= U ∧ 0 < P ∧ v ≠ (0, 0) ∧ HighwayFrom s U P v ∧
      forall n, U <= n -> readColor s (n + P) = readColor s n := by
  obtain ⟨n, m, hn, hnW, hnm, he⟩ := memoryKey_repeats s T W
  have hh := highwayFrom_of_memoryKey_eq h hn hnW hnm he
  exact ⟨n, m - n, _, hn, by omega, hh.drift_ne_zero (by omega), hh,
    fun _ ht => hh.reads_periodic ht⟩

theorem EventuallyBoundedMemory.highway {s : State} (h : EventuallyBoundedMemory s) :
    exists T P v, 0 < P ∧ v ≠ (0, 0) ∧ HighwayFrom s T P v ∧
      forall n, T <= n -> readColor s (n + P) = readColor s n := by
  obtain ⟨T, W, h⟩ := h
  obtain ⟨U, P, v, _, hP, hv, hh, hr⟩ := h.highway
  exact ⟨U, P, v, hP, hv, hh, hr⟩

end LangtonsAnt
