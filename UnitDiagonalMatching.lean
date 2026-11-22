import UnitDiagonalRank

/-! Enumeration of layer ranks and ordered matching of directed phase events. -/
namespace LangtonsAnt

private theorem nodup_map_on {α β : Type} {xs : List α} {f : α → β}
    (hn : xs.Nodup)
    (hf : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨b, hb, he⟩ := List.mem_map.mp h
      have := hf b (by simp [hb]) a (by simp) he
      subst b
      exact ha hb
    · exact ih hn (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy]))

/-- An order-preserving bijection preserves the number of strict predecessors.
The relations are arbitrary: in applications they compare stable times. -/
theorem ordered_bijection_position {α β : Type} (xs : List α) (ys : List β)
    (f : α → β) (R : α → α → Prop) (S : β → β → Prop)
    [DecidableRel R] [DecidableRel S]
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y)
    (honto : ∀ y, y ∈ ys ↔ ∃ x ∈ xs, f x = y)
    (horder : ∀ x ∈ xs, ∀ y ∈ xs, R x y ↔ S (f x) (f y))
    {i : α} (hi : i ∈ xs) :
    (xs.filter (fun x => decide (R x i))).length =
      (ys.filter (fun y => decide (S y (f i)))).length := by
  have hp : (xs.map f).Perm ys := by
    apply (List.perm_ext_iff_of_nodup (nodup_map_on hx hinj) hy).mpr
    intro y
    simpa only [List.mem_map] using (honto y).symm
  have he : xs.filter (fun x => decide (R x i)) =
      xs.filter (fun x => decide (S (f x) (f i))) := by
    apply List.filter_congr
    intro x hmem
    exact Bool.eq_iff_iff.mpr (by simpa using horder x hmem i hi)
  rw [he]
  simpa only [List.filter_map, List.length_map, Function.comp_def] using
    (hp.filter (fun y => decide (S y (f i)))).length_eq

theorem layerPhases_nodup (P : Nat) (w : Nat → Bool) (L : Int) :
    (layerPhases P w L).Nodup := List.nodup_range.filter _

theorem stableRank_lt_layer_length {P i : Nat} {w : Nat → Bool} {L : Int}
    (hd : wordDrift P w = (1, -1)) (hi : i ∈ layerPhases P w L) :
    stableRank P w i < (layerPhases P w L).length := by
  obtain ⟨hiP, hiL⟩ := mem_layerPhases.mp hi
  have hn : (i :: priorPhases P w i).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, priorPhases_nodup P w i⟩
    simp [mem_priorPhases_iff_stableTime hd hiP]
  have hs : i :: priorPhases P w i ⊆ layerPhases P w L := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · obtain ⟨hjP, hjL, _⟩ := (mem_priorPhases_iff_stableTime hd hiP).mp hj
      exact mem_layerPhases.mpr ⟨hjP, hjL.trans hiL⟩
  have := hn.length_le_of_subset hs
  simpa only [List.length_cons, stableRank, Nat.succ_le_iff] using this

theorem stableRank_injective_on_layer {P i j : Nat} {w : Nat → Bool} {L : Int}
    (hd : wordDrift P w = (1, -1)) (hi : i ∈ layerPhases P w L)
    (hj : j ∈ layerPhases P w L) (he : stableRank P w i = stableRank P w j) :
    i = j := by
  obtain ⟨hiP, hiL⟩ := mem_layerPhases.mp hi
  obtain ⟨hjP, hjL⟩ := mem_layerPhases.mp hj
  have h1 := stableRank_lt_iff_stableTime_lt hd hiP hjP (hiL.trans hjL.symm)
  have h2 := stableRank_lt_iff_stableTime_lt hd hjP hiP (hjL.trans hiL.symm)
  apply stableTime_injective (w := w) hiP hjP
  omega

theorem stableRank_surjective_on_layer {P r : Nat} {w : Nat → Bool} {L : Int}
    (hd : wordDrift P w = (1, -1)) (hr : r < (layerPhases P w L).length) :
    ∃ i ∈ layerPhases P w L, stableRank P w i = r := by
  let xs := (layerPhases P w L).map (stableRank P w)
  have hn : xs.Nodup := nodup_map_on (layerPhases_nodup P w L)
    (fun _ hi _ hj => stableRank_injective_on_layer hd hi hj)
  have hs : xs ⊆ List.range (layerPhases P w L).length := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (stableRank_lt_layer_length hd hi)
  have hm : r ∈ xs := by
    by_cases hnot : r ∈ xs
    · exact hnot
    apply False.elim
    have hn' := List.nodup_cons.mpr ⟨hnot, hn⟩
    have hs' : r :: xs ⊆ List.range (layerPhases P w L).length := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_range.mpr hr
      · exact hs hx
    have hh := hn'.length_le_of_subset hs'
    simp only [List.length_cons, List.length_range, xs, List.length_map] at hh
    omega
  exact List.mem_map.mp hm

namespace UnitDiagonalMatching

def inDir (w : Nat → Bool) (i : Nat) : Direction := (wordTrace w i).2
def outDir (w : Nat → Bool) (i : Nat) : Direction := turn (w i) (inDir w i)
def succ (P i : Nat) : Nat := (i + 1) % P
def pred (P j : Nat) : Nat := if j = 0 then P - 1 else j - 1

/-- Change of layer along the indicated direction. -/
def layerStep : Direction → Int
  | .north | .east => 1
  | .south | .west => -1

/-- Horizontal displacement; also the drift coefficient in the basepoint formula. -/
def delta : Direction → Int
  | .east => 1
  | .west => -1
  | .north | .south => 0

theorem succ_lt {P i : Nat} (hP : 0 < P) : succ P i < P := Nat.mod_lt _ hP

theorem pred_lt {P j : Nat} (hj : j < P) : pred P j < P := by
  unfold pred
  split <;> omega

theorem pred_succ {P i : Nat} (hi : i < P) : pred P (succ P i) = i := by
  by_cases h : i + 1 < P
  · simp only [succ, Nat.mod_eq_of_lt h, pred, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    omega
  · have he : i + 1 = P := by omega
    simp [succ, he, pred]
    omega

theorem succ_pred {P j : Nat} (hj : j < P) : succ P (pred P j) = j := by
  by_cases hz : j = 0
  · subst j
    simp only [pred, ite_true, succ]
    rw [show P - 1 + 1 = P by omega, Nat.mod_self]
  · simp only [pred, hz, ite_false, succ]
    rw [show j - 1 + 1 = j by omega, Nat.mod_eq_of_lt hj]

theorem succ_injective {P i j : Nat} (hi : i < P) (hj : j < P)
    (he : succ P i = succ P j) : i = j := by
  have := congrArg (pred P) he
  simpa only [pred_succ hi, pred_succ hj] using this

theorem layer_move (p : Point) (d : Direction) :
    layer (move p d) = layer p + layerStep d := by
  cases d <;> simp [layer, weight, move, layerStep] <;> omega

theorem x_move (p : Point) (d : Direction) : (move p d).1 = p.1 + delta d := by
  cases d <;> simp [move, delta] <;> omega

theorem basepoint_move (L : Int) (d : Direction) :
    move (0, L) d = addPoint (0, L + layerStep d) (scalePoint (1, -1) (delta d)) := by
  cases d <;> apply Prod.ext <;> simp [move, layerStep, addPoint, scalePoint, delta] <;> omega

theorem successor_heading {P i : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hi : i < P) :
    inDir w (succ P i) = outDir w i := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i 1
  have h0 : p.phase 0 = i := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have h1 : p.phase 1 = succ P i := rfl
  simpa only [h0, h1, inDir, outDir] using p.heading_step hh (r := 0) (by omega)

theorem successor_layer {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    layer (wordPos w (succ P i)) = layer (wordPos w i) + layerStep (outDir w i) := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i 1
  have h0 : p.phase 0 = i := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have h1 : p.phase 1 = succ P i := rfl
  have hs := p.pos_step (w := w) (r := 0) (by omega)
  have hl := congrArg layer hs
  rw [layer_move, p.layer_pos hd 1, p.layer_pos hd 0, h0, h1] at hl
  exact hl

/-- The seam carry cancels out of stable time, leaving a direction-only shift. -/
theorem successor_stableTime {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    stableTime P w (succ P i) = stableTime P w i + 1 - (P : Int) * delta (outDir w i) := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i 1
  have h0 : p.phase 0 = i := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have h1 : p.phase 1 = succ P i := rfl
  have ht := p.time_step 0 (by omega)
  have hx := congrArg Prod.fst (p.pos_step (w := w) (r := 0) (by omega))
  rw [x_move] at hx
  have t0 := p.stableTime_eq hd 0
  have t1 := p.stableTime_eq hd 1
  rw [hx, Int.mul_add] at t1
  simp only [h0, h1] at ht t0 t1
  change _ = _ - ((P : Int) * (p.pos w 0).1 + (P : Int) * delta (outDir w i)) at t1
  simp only [Nat.zero_add] at ht
  omega

def departures (P : Nat) (w : Nat → Bool) (L : Int) (d : Direction) : List Nat :=
  (layerPhases P w L).filter (fun i => decide (outDir w i = d))

def arrivals (P : Nat) (w : Nat → Bool) (L : Int) (d : Direction) : List Nat :=
  (layerPhases P w L).filter (fun i => decide (inDir w i = d))

theorem mem_departures {P i : Nat} {w : Nat → Bool} {L : Int} {d : Direction} :
    i ∈ departures P w L d ↔ i < P ∧ layer (wordPos w i) = L ∧ outDir w i = d := by
  simp [departures, mem_layerPhases, and_assoc]

theorem mem_arrivals {P i : Nat} {w : Nat → Bool} {L : Int} {d : Direction} :
    i ∈ arrivals P w L d ↔ i < P ∧ layer (wordPos w i) = L ∧ inDir w i = d := by
  simp [arrivals, mem_layerPhases, and_assoc]

theorem departures_nodup (P : Nat) (w : Nat → Bool) (L : Int) (d : Direction) :
    (departures P w L d).Nodup := (layerPhases_nodup P w L).filter _

theorem arrivals_nodup (P : Nat) (w : Nat → Bool) (L : Int) (d : Direction) :
    (arrivals P w L d).Nodup := (layerPhases_nodup P w L).filter _

theorem successor_mem_iff {P i : Nat} {w : Nat → Bool} {L : Int} {d : Direction}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (1, -1)) (hi : i < P) :
    succ P i ∈ arrivals P w (L + layerStep d) d ↔ i ∈ departures P w L d := by
  rw [mem_arrivals, mem_departures, successor_heading hh hi, successor_layer hd hi]
  constructor
  · rintro ⟨_, hl, ho⟩
    rw [ho] at hl
    exact ⟨hi, by omega, ho⟩
  · rintro ⟨_, hl, ho⟩
    exact ⟨succ_lt (by omega), by rw [hl, ho], ho⟩

theorem predecessor_mem {P j : Nat} {w : Nat → Bool} {L : Int} {d : Direction}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (1, -1))
    (hj : j ∈ arrivals P w (L + layerStep d) d) : pred P j ∈ departures P w L d := by
  have hjP := (mem_arrivals.mp hj).1
  apply (successor_mem_iff hh hd (pred_lt hjP)).mp
  simpa only [succ_pred hjP] using hj

/-- Successor maps departures onto arrivals, with cyclic predecessor as its inverse. -/
theorem successor_bijection {P : Nat} {w : Nat → Bool} (L : Int) (d : Direction)
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (1, -1)) :
    (∀ i ∈ departures P w L d,
      succ P i ∈ arrivals P w (L + layerStep d) d ∧ pred P (succ P i) = i) ∧
    (∀ j ∈ arrivals P w (L + layerStep d) d,
      pred P j ∈ departures P w L d ∧ succ P (pred P j) = j) := by
  constructor
  · intro i hi
    have hiP := (mem_departures.mp hi).1
    exact ⟨(successor_mem_iff hh hd hiP).mpr hi, pred_succ hiP⟩
  · intro j hj
    exact ⟨predecessor_mem hh hd hj, succ_pred (mem_arrivals.mp hj).1⟩

theorem successor_onto {P : Nat} {w : Nat → Bool} {L : Int} {d : Direction}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (1, -1)) (j : Nat) :
    j ∈ arrivals P w (L + layerStep d) d ↔
      ∃ i ∈ departures P w L d, succ P i = j := by
  constructor
  · intro hj
    exact ⟨pred P j, predecessor_mem hh hd hj, succ_pred (mem_arrivals.mp hj).1⟩
  · rintro ⟨i, hi, rfl⟩
    exact (successor_mem_iff hh hd (mem_departures.mp hi).1).mpr hi

theorem successor_stableTime_order {P i j : Nat} {w : Nat → Bool} {d : Direction}
    (hd : wordDrift P w = (1, -1)) (hi : i < P) (hj : j < P)
    (hoi : outDir w i = d) (hoj : outDir w j = d) :
    stableTime P w i < stableTime P w j ↔
      stableTime P w (succ P i) < stableTime P w (succ P j) := by
  rw [successor_stableTime hd hi, successor_stableTime hd hj, hoi, hoj]
  omega

/-- The zero-based position in the departure time order is the arrival position. -/
theorem departure_position_eq_arrival_position {P i : Nat} {w : Nat → Bool}
    {L : Int} {d : Direction} (hh : (wordTrace w P).2 = .north)
    (hd : wordDrift P w = (1, -1)) (hi : i ∈ departures P w L d) :
    ((departures P w L d).filter (fun j => decide (stableTime P w j < stableTime P w i))).length =
    ((arrivals P w (L + layerStep d) d).filter
      (fun j => decide (stableTime P w j < stableTime P w (succ P i)))).length := by
  apply ordered_bijection_position _ _ (succ P)
    (fun j k => stableTime P w j < stableTime P w k)
    (fun j k => stableTime P w j < stableTime P w k)
    (departures_nodup P w L d) (arrivals_nodup P w (L + layerStep d) d)
    (fun _ hj _ hk => succ_injective (mem_departures.mp hj).1 (mem_departures.mp hk).1)
    (successor_onto hh hd) _ hi
  intro j hj k hk
  obtain ⟨hjP, _, hjd⟩ := mem_departures.mp hj
  obtain ⟨hkP, _, hkd⟩ := mem_departures.mp hk
  exact successor_stableTime_order hd hjP hkP hjd hkd

/-- The same directed matching is increasing when events are named by layer ranks. -/
theorem successor_rank_order {P i j : Nat} {w : Nat → Bool} {L : Int} {d : Direction}
    (hd : wordDrift P w = (1, -1))
    (hi : i ∈ departures P w L d) (hj : j ∈ departures P w L d) :
    stableRank P w i < stableRank P w j ↔
      stableRank P w (succ P i) < stableRank P w (succ P j) := by
  obtain ⟨hiP, hiL, hid⟩ := mem_departures.mp hi
  obtain ⟨hjP, hjL, hjd⟩ := mem_departures.mp hj
  have hl : layer (wordPos w (succ P i)) = layer (wordPos w (succ P j)) := by
    rw [successor_layer hd hiP, successor_layer hd hjP, hiL, hjL, hid, hjd]
  rw [stableRank_lt_iff_stableTime_lt hd hiP hjP (hiL.trans hjL.symm),
    stableRank_lt_iff_stableTime_lt hd (succ_lt (by omega)) (succ_lt (by omega)) hl]
  exact successor_stableTime_order hd hiP hjP hid hjd

theorem departure_rank_position_eq_arrival_rank_position {P i : Nat} {w : Nat → Bool}
    {L : Int} {d : Direction} (hh : (wordTrace w P).2 = .north)
    (hd : wordDrift P w = (1, -1)) (hi : i ∈ departures P w L d) :
    ((departures P w L d).filter (fun j => decide (stableRank P w j < stableRank P w i))).length =
    ((arrivals P w (L + layerStep d) d).filter
      (fun j => decide (stableRank P w j < stableRank P w (succ P i)))).length := by
  exact ordered_bijection_position _ _ (succ P)
    (fun j k => stableRank P w j < stableRank P w k)
    (fun j k => stableRank P w j < stableRank P w k)
    (departures_nodup P w L d) (arrivals_nodup P w (L + layerStep d) d)
    (fun _ hj _ hk => succ_injective (mem_departures.mp hj).1 (mem_departures.mp hk).1)
    (successor_onto hh hd) (fun _ hj _ hk => successor_rank_order hd hj hk) hi

end UnitDiagonalMatching

end LangtonsAnt




