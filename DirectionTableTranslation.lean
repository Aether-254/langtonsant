import DriftRank

/-!
# Translations preserving the ordered direction tables commute with the successor

For a consistent periodic word with nonzero full drift `v`, suppose a spatial translation `b`
preserves every rank-indexed incoming-direction table (`PreservesTables`).  Sending each phase to
the phase of the translated class with the same stable rank (`F`) then commutes with the cyclic
successor (`F_succ`).  For `v = (m,-m)` and `b = (a,-a)` this is lane translation at a fixed layer
(`diagonal_F_succ`), the first step of the brainstorm-2 T2 programme for excluding `(m,-m)`
(`research/brainstorm2-T2-diagonal-multiples-2026-11-22.md`).  Single-cycle and minimal-period
arithmetic are not included.

Pure kernel proofs; no `native_decide`.
-/

namespace LangtonsAnt.DirectionTableTranslation

/-- Rank-indexed entry of the ordered incoming-direction table. Absent ranks,
including all ranks of an empty class, have no entry. -/
def TableEntry (v : Point) (P : Nat) (w : Nat → Bool)
    (c : Point) (r : Nat) (d : Direction) : Prop :=
  ∃ i ∈ Drift.classPhases v P w c,
    Drift.stableRank P w i = r ∧ Drift.inDir w i = d

/-- Equality of every ordered table under a spatial translation. For
v = (m,-m), b = (a,-a), this is precisely lane translation at fixed layer.
Rank labels retain order; this is stronger than equality of direction counts. -/
def PreservesTables (v : Point) (P : Nat) (w : Nat → Bool) (b : Point) : Prop :=
  ∀ c r d, TableEntry v P w c r d ↔ TableEntry v P w (addPoint c b) r d

theorem preservesTables_zero (v : Point) (P : Nat) (w : Nat → Bool) :
    PreservesTables v P w (0, 0) := by
  intro c r d
  simp [addPoint]

private theorem translate_class {v p q : Point} (b : Point)
    (h : Drift.SameClass v p q) :
    Drift.SameClass v (addPoint p b) (addPoint q b) := by
  obtain ⟨z, rfl⟩ := h
  refine ⟨z, ?_⟩
  apply Prod.ext <;> simp [addPoint, scalePoint] <;> omega

private theorem move_translate (p b : Point) (d : Direction) :
    move (addPoint p b) d = addPoint (move p d) b := by
  cases d <;> apply Prod.ext <;> simp [move, addPoint] <;> omega

private theorem image_exists {v b : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) {i : Nat} (hi : i < P) :
    ∃ j ∈ Drift.classPhases v P w (addPoint (wordPos w i) b),
      Drift.stableRank P w j = Drift.stableRank P w i := by
  obtain ⟨j, hj, hr, _⟩ := (h (wordPos w i) _ (Drift.inDir w i)).mp
    ⟨i, Drift.mem_classPhases.mpr ⟨hi, Drift.SameClass.refl _ _⟩, rfl, rfl⟩
  exact (Drift.stableRank_bijection_on_class hd hv).2.2 _
    (hr ▸ Drift.stableRank_lt_class_length hd hv hj)

/-- Target class, same stable rank; outside the phase range, use identity. -/
noncomputable def F {v : Point} {P : Nat} {w : Nat → Bool} {b : Point}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) (i : Nat) : Nat :=
  if hi : i < P then Classical.choose (image_exists hd hv h hi) else i

theorem F_spec {v b : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) (hi : i < P) :
    F hd hv h i ∈ Drift.classPhases v P w (addPoint (wordPos w i) b) ∧
      Drift.stableRank P w (F hd hv h i) = Drift.stableRank P w i := by
  simpa only [F, dite_eq_left hi] using Classical.choose_spec (image_exists hd hv h hi)

private theorem F_class {v b c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) (hi : i ∈ Drift.classPhases v P w c) :
    F hd hv h i ∈ Drift.classPhases v P w (addPoint c b) := by
  obtain ⟨hiP, hic⟩ := Drift.mem_classPhases.mp hi
  obtain ⟨hjP, hjc⟩ := Drift.mem_classPhases.mp (F_spec hd hv h hiP).1
  exact Drift.mem_classPhases.mpr ⟨hjP, hjc.trans (translate_class b hic)⟩

theorem F_inDir {v b : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) (hi : i < P) :
    Drift.inDir w (F hd hv h i) = Drift.inDir w i := by
  obtain ⟨j, hj, hr, he⟩ := (h (wordPos w i) _ (Drift.inDir w i)).mp
    ⟨i, Drift.mem_classPhases.mpr ⟨hi, Drift.SameClass.refl _ _⟩, rfl, rfl⟩
  have eqj := Drift.stableRank_injective_on_class hd hv
    (F_spec hd hv h hi).1 hj ((F_spec hd hv h hi).2.trans hr.symm)
  exact eqj ▸ he

theorem F_color {v b : Point} {P i : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) (hi : i < P) :
    w (F hd hv h i) = w i := by
  rw [Drift.consistentWord_stableRank_color hw
    (Drift.mem_classPhases.mp (F_spec hd hv h hi).1).1,
    Drift.consistentWord_stableRank_color hw hi, (F_spec hd hv h hi).2]

theorem F_outDir {v b : Point} {P i : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) (hi : i < P) :
    Drift.outDir w (F hd hv h i) = Drift.outDir w i := by
  change turn (w (F hd hv h i)) (Drift.inDir w (F hd hv h i)) =
    turn (w i) (Drift.inDir w i)
  rw [F_color hw hd hv h hi, F_inDir hd hv h hi]

private theorem F_onto_class {v b c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) {j : Nat}
    (hj : j ∈ Drift.classPhases v P w (addPoint c b)) :
    ∃ i ∈ Drift.classPhases v P w c, F hd hv h i = j := by
  obtain ⟨i, hi, hr, _⟩ := (h c _ (Drift.inDir w j)).mpr ⟨j, hj, rfl, rfl⟩
  refine ⟨i, hi, Drift.stableRank_injective_on_class hd hv (F_class hd hv h hi) hj ?_⟩
  exact (F_spec hd hv h (Drift.mem_classPhases.mp hi).1).2.trans hr

private theorem port_position {v b c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) (q : Nat → Bool)
    (hq : ∀ i, i < P → q (F hd hv h i) = q i)
    (hi : i ∈ (Drift.classPhases v P w c).filter q) :
    (((Drift.classPhases v P w c).filter q).filter
      (fun j => decide (Drift.stableRank P w j < Drift.stableRank P w i))).length =
    (((Drift.classPhases v P w (addPoint c b)).filter q).filter
      (fun j => decide (Drift.stableRank P w j < Drift.stableRank P w (F hd hv h i)))).length := by
  apply ordered_bijection_position _ _ (F hd hv h)
    (fun j k => Drift.stableRank P w j < Drift.stableRank P w k)
    (fun j k => Drift.stableRank P w j < Drift.stableRank P w k)
    ((Drift.classPhases_nodup _ _ _ _).filter _)
    ((Drift.classPhases_nodup _ _ _ _).filter _)
    ?_ ?_ ?_ hi
  · intro j hj k hk he
    have hjc := (List.mem_filter.mp hj).1
    have hkc := (List.mem_filter.mp hk).1
    apply Drift.stableRank_injective_on_class hd hv hjc hkc
    rw [← (F_spec hd hv h (Drift.mem_classPhases.mp hjc).1).2,
      ← (F_spec hd hv h (Drift.mem_classPhases.mp hkc).1).2, he]
  · intro j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := F_onto_class hd hv h (List.mem_filter.mp hj).1
      exact ⟨i, List.mem_filter.mpr ⟨hi, by
        rw [← hq i (Drift.mem_classPhases.mp hi).1]
        exact (List.mem_filter.mp hj).2⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact List.mem_filter.mpr ⟨F_class hd hv h (List.mem_filter.mp hi).1, by
        rw [hq i (Drift.mem_classPhases.mp (List.mem_filter.mp hi).1).1]
        exact (List.mem_filter.mp hi).2⟩
  · intro j hj k hk
    rw [(F_spec hd hv h (Drift.mem_classPhases.mp (List.mem_filter.mp hj).1).1).2,
      (F_spec hd hv h (Drift.mem_classPhases.mp (List.mem_filter.mp hk).1).1).2]

private theorem position_injective (xs : List Nat) (rank : Nat → Nat)
    (hn : xs.Nodup) {i j : Nat} (hi : i ∈ xs) (hj : j ∈ xs)
    (he : (xs.filter (fun k => decide (rank k < rank i))).length =
      (xs.filter (fun k => decide (rank k < rank j))).length) : rank i = rank j := by
  have strict : ∀ a ∈ xs, ∀ b ∈ xs, rank a < rank b →
      (xs.filter (fun k => decide (rank k < rank a))).length <
      (xs.filter (fun k => decide (rank k < rank b))).length := by
    intro a ha b _ hab
    have nd : (a :: xs.filter (fun k => decide (rank k < rank a))).Nodup :=
      List.nodup_cons.mpr ⟨by simp, hn.filter _⟩
    have sub : a :: xs.filter (fun k => decide (rank k < rank a)) ⊆
        xs.filter (fun k => decide (rank k < rank b)) := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · simp [ha, hab]
      · obtain ⟨hk, hka⟩ := List.mem_filter.mp hk
        exact List.mem_filter.mpr ⟨hk, by simpa using Nat.lt_trans (of_decide_eq_true hka) hab⟩
    have := nd.length_le_of_subset sub
    simp only [List.length_cons] at this
    omega
  have h1 := strict i hi j hj
  have h2 := strict j hj i hi
  omega

/-- Every ordered-table translation commutes with the cyclic phase successor.
The result holds for any nonzero full drift and any spatial translation. -/
theorem F_succ {v b : Point} {P i : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (h : PreservesTables v P w b) (hi : i < P) :
    F hd hv h (Drift.succ P i) = Drift.succ P (F hd hv h i) := by
  let c := wordPos w i
  let c' := wordPos w (Drift.succ P i)
  let d := Drift.outDir w i
  have hp : 0 < P := by omega
  have hsi : Drift.succ P i < P := UnitDiagonalMatching.succ_lt hp
  have hfi : F hd hv h i < P := (Drift.mem_classPhases.mp (F_spec hd hv h hi).1).1
  have hsfi : Drift.succ P (F hd hv h i) < P := UnitDiagonalMatching.succ_lt hp
  have ht : Drift.SameClass v (move c d) c' := (Drift.successor_class hd hi).symm
  have htt : Drift.SameClass v (move (addPoint c b) d) (addPoint c' b) := by
    rw [move_translate]
    exact translate_class b ht
  have hdep : i ∈ Drift.departures v P w c d :=
    Drift.mem_departures.mpr ⟨hi, Drift.SameClass.refl _ _, rfl⟩
  have hfdep : F hd hv h i ∈ Drift.departures v P w (addPoint c b) d :=
    Drift.mem_departures.mpr ⟨hfi,
      (Drift.mem_classPhases.mp (F_spec hd hv h hi).1).2, F_outDir hw hd hv h hi⟩
  have harr : Drift.succ P i ∈ Drift.arrivals v P w c' d :=
    Drift.mem_arrivals.mpr ⟨hsi, Drift.SameClass.refl _ _, Drift.successor_heading hw.1 hi⟩
  have hfarr : F hd hv h (Drift.succ P i) ∈
      Drift.arrivals v P w (addPoint c' b) d := by
    apply Drift.mem_arrivals.mpr
    exact ⟨(Drift.mem_classPhases.mp (F_spec hd hv h hsi).1).1,
      (Drift.mem_classPhases.mp (F_spec hd hv h hsi).1).2,
      (F_inDir hd hv h hsi).trans (Drift.successor_heading hw.1 hi)⟩
  have hsfarr : Drift.succ P (F hd hv h i) ∈
      Drift.arrivals v P w (addPoint c' b) d := by
    have hc := (Drift.successor_target_sameClass hd hfdep).symm.trans htt
    exact Drift.mem_arrivals.mpr ⟨hsfi, hc,
      (Drift.successor_heading hw.1 hfi).trans (F_outDir hw hd hv h hi)⟩
  have orig := Drift.departure_rank_position_eq_arrival_rank_position_of_target
    hw.1 hd hv ht hdep
  have translated := Drift.departure_rank_position_eq_arrival_rank_position_of_target
    hw.1 hd hv htt hfdep
  have dep := port_position hd hv h (fun j => decide (Drift.outDir w j = d))
    (fun j hj => by rw [F_outDir hw hd hv h hj]) hdep
  have arr := port_position hd hv h (fun j => decide (Drift.inDir w j = d))
    (fun j hj => by rw [F_inDir hd hv h hj]) harr
  have he := arr.symm.trans (orig.symm.trans (dep.trans translated))
  have hr := position_injective _ (Drift.stableRank P w)
    (Drift.arrivals_nodup _ _ _ _ _) hfarr hsfarr he
  exact Drift.stableRank_injective_on_class hd hv
    (List.mem_filter.mp hfarr).1 (List.mem_filter.mp hsfarr).1 hr

/-- Diagonal specialization: b = (a,-a) fixes x+y and shifts x mod m by a. -/
theorem diagonal_F_succ {m a : Int} {P i : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hd : wordDrift P w = (m, -m))
    (hm : 0 < m) (h : PreservesTables (m, -m) P w (a, -a)) (hi : i < P) :
    F hd (by intro he; have := congrArg Prod.fst he; simp at this; omega) h
      (Drift.succ P i) =
    Drift.succ P (F hd (by intro he; have := congrArg Prod.fst he; simp at this; omega) h i) :=
  F_succ hw hd _ h hi

/-- Zero translation really induces the identity, for every nonzero-drift word. -/
theorem F_zero {v : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (hi : i < P) :
    F hd hv (preservesTables_zero v P w) i = i := by
  have hs := F_spec hd hv (preservesTables_zero v P w) hi
  apply Drift.stableRank_injective_on_class hd hv (c := wordPos w i)
  · simpa [addPoint] using hs.1
  · exact Drift.mem_classPhases.mpr ⟨hi, Drift.SameClass.refl _ _⟩
  · exact hs.2

end LangtonsAnt.DirectionTableTranslation
