import SpacedHighwayClassification

namespace LangtonsAnt

example : (spacedObstacles 1).pos = (0, 0) ∧ (spacedObstacles 1).dir = .north := ⟨rfl, rfl⟩

example : (spacedObstacles 1).board (-68, -42) = true := by
  apply (spacedObstacles_black 1 _).mpr
  exact ⟨0, rfl⟩

example : (spacedObstacles 1).board (-78, -52) = true := by
  apply (spacedObstacles_black 1 _).mpr
  exact ⟨1, rfl⟩

-- Reject a preceding point, an intermediate point, and a point off the ray.
example : (spacedObstacles 1).board (-58, -32) = false := by
  cases h : (spacedObstacles 1).board (-58, -32)
  · rfl
  · obtain ⟨i, hi⟩ := (spacedObstacles_black 1 _).mp h
    simp only [Prod.mk.injEq] at hi
    omega

example : (spacedObstacles 1).board (-76, -50) = false := by
  cases h : (spacedObstacles 1).board (-76, -50)
  · rfl
  · obtain ⟨i, hi⟩ := (spacedObstacles_black 1 _).mp h
    simp only [Prod.mk.injEq] at hi
    omega

example : (spacedObstacles 1).board (-78, -51) = false := by
  cases h : (spacedObstacles 1).board (-78, -51)
  · rfl
  · obtain ⟨i, hi⟩ := (spacedObstacles_black 1 _).mp h
    simp only [Prod.mk.injEq] at hi
    omega

example : HighwayFrom (spacedObstacles 1) 12496 652 (-10, -10) := spacedObstacles_highway 1
example : HighwayFrom (spacedObstacles 2) 12496 756 (-12, -12) := spacedObstacles_highway 2
example : HighwayFrom (spacedObstacles 10) 12496 1588 (-28, -28) := spacedObstacles_highway 10

example (T : Nat) (v : Point) : ¬HighwayFrom (spacedObstacles 1) T 104 v :=
  spacedObstacles_no_period104 1 T v

example (T : Nat) : ¬HighwayFrom (spacedObstacles 1) T 548 (-8, -8) :=
  spacedObstacles_no_other_spacing (k := 1) (l := 0) (by decide)

-- A concrete member has no positive eventual period at most one million.
example (T Q : Nat) (w : Point) (hQ : 0 < Q) (hB : Q <= 1000000) :
    ¬HighwayFrom (spacedObstacles 2000000) T Q w :=
  (spacedObstacles_unbounded_periods 1000000).2 T Q w hQ hB

-- The old 548-step state is exactly the k=0 member, including its initial board.
example : spacedObstacles 0 = infiniteObstacles := spacedObstacles_zero

example (T q : Nat) (hq : 0 < q) (hsmall : q < 548) (v : Point) :
    ¬HighwayFrom (spacedObstacles 0) T q v := by
  rw [spacedObstacles_zero]
  exact infiniteObstacles_no_short_tail T q hq hsmall v

-- Reject every smaller period even after discarding an arbitrary initial segment.
example (k T q : Nat) (hq : 0 < q) (hs : q < 548 + 104 * k) (v : Point) :
    ¬HighwayFrom (spacedObstacles k) T q v := spacedObstacles_no_short_tail k T q hq hs v

example (T : Nat) (v : Point) : ¬HighwayFrom (spacedObstacles 1) T 326 v :=
  spacedObstacles_no_short_tail 1 T 326 (by decide) (by decide) v

example (T : Nat) (v : Point) : ¬HighwayFrom (spacedObstacles 2) T 378 v :=
  spacedObstacles_no_short_tail 2 T 378 (by decide) (by decide) v

-- Multiples really occur, with the corresponding displacement multiplied as well.
example : exists T, HighwayFrom (spacedObstacles 1) T 1304 (-20, -20) := by
  apply (spacedObstacles_highway_iff 1 1304 (-20, -20)).mpr
  exact ⟨2, rfl, rfl⟩

example : ¬(exists T, HighwayFrom (spacedObstacles 1) T 1304 (-10, -10)) := by
  intro h
  obtain ⟨m, hQ, hv⟩ := (spacedObstacles_highway_iff 1 1304 (-10, -10)).mp h
  have hm : m = 2 := by change 1304 = 652 * m at hQ; omega
  subst m
  have hfalse : (-10 : Int) = -20 := congrArg Prod.fst hv
  omega

-- Marker alignment includes the wrap into the next cycle and excludes adjacent phases.
example (k : Nat) :
    HasCollisionMarker (fun j => readColor (spacedObstacles k) (12496 + j)) (spacedPeriod k + 107) := by
  apply (spacedObstacles_marker_iff k _).mpr
  have hP : 107 < spacedPeriod k := by unfold spacedPeriod; omega
  simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hP]

example (k : Nat) : ¬HasCollisionMarker (spacedColor k) 106 := by
  intro h
  have he := (collisionMarker_iff k 106).mp h
  have hP : 106 < spacedPeriod k := by unfold spacedPeriod; omega
  rw [Nat.mod_eq_of_lt hP] at he
  contradiction

example (k Q : Nat) :
    (exists T, forall n, T <= n -> readColor (spacedObstacles k) (n + Q) =
      readColor (spacedObstacles k) n) ↔ spacedPeriod k ∣ Q := spacedObstacles_read_period_iff k Q

end LangtonsAnt
