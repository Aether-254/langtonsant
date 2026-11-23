import DirectionTableTranslation
import RootWord

namespace LangtonsAnt.PersistA.TranslationShift

theorem commuting_shift {P : Nat} (hP : 0 < P) (F : Nat → Nat)
    (hF : ∀ i, i < P → F i < P)
    (hc : ∀ i, i < P → F (Drift.succ P i) = Drift.succ P (F i)) :
    ∀ i, i < P → F i = (F 0 + i) % P := by
  intro i
  induction i with
  | zero => intro _; simp [Nat.mod_eq_of_lt (hF 0 hP)]
  | succ i ih =>
      intro hi
      have hip : i < P := by omega
      have hs : Drift.succ P i = i+1 := by
        simp [Drift.succ, UnitDiagonalMatching.succ, Nat.mod_eq_of_lt hi]
      calc
        F (i + 1) = F (Drift.succ P i) := congrArg F hs.symm
        _ = Drift.succ P (F i) := hc i hip
        _ = (F 0 + (i + 1)) % P := by
          rw [ih hip]
          simp only [Drift.succ, UnitDiagonalMatching.succ, Nat.mod_add_mod, Nat.add_assoc]

theorem involutive_shift_half {P q : Nat} (_hP : 0 < P)
    (hq : q < P) (hne : q ≠ 0) (h : (q+q)%P=0) :
    q+q=P := by
  have hq0 : 0 < q := by omega
  have hlt : q+q < P+P := by omega
  by_cases hsmall : q+q < P
  · rw [Nat.mod_eq_of_lt hsmall] at h
    omega
  · have hqle : P ≤ q+q := by omega
    have hh : (q+q)%P = q+q-P := by
      rw [Nat.mod_eq_sub_mod hqle, Nat.mod_eq_of_lt (show q+q-P < P by omega)]
    omega


theorem no_half_drift_table_symmetry {P : Nat} {w : Nat → Bool}
    (hw : ConsistentWord P w) (hP : 0 < P) (hd : wordDrift P w = (2, -2)) :
    ¬ DirectionTableTranslation.PreservesTables (2, -2) P w (1, -1) := by
  intro hsym
  have hv : ((2 : Int), (-2 : Int)) ≠ (0, 0) := by decide
  let f := DirectionTableTranslation.F hd hv hsym
  have hspec := fun i hi => DirectionTableTranslation.F_spec hd hv hsym (i := i) hi
  have hf : ∀ i, i < P → f i < P := by
    intro i hi
    exact (Drift.mem_classPhases.mp (hspec i hi).1).1
  have hshift : ∀ i, i < P → f i = (f 0 + i) % P :=
    commuting_shift hP f hf (fun i hi => DirectionTableTranslation.F_succ hw hd hv hsym hi)
  have hinvolution : ∀ i, i < P → f (f i) = i := by
    intro i hi
    have hi1 := hspec i hi
    have hi2 := hspec (f i) (hf i hi)
    obtain ⟨_, z0, hz0⟩ := Drift.mem_classPhases.mp hi1.1
    obtain ⟨hffi, z1, hz1⟩ := Drift.mem_classPhases.mp hi2.1
    have hclass : Drift.SameClass (2, -2) (wordPos w (f (f i))) (wordPos w i) := by
      refine ⟨z0 + z1 - 1, ?_⟩
      have hx0 := congrArg Prod.fst hz0
      have hy0 := congrArg Prod.snd hz0
      have hx1 := congrArg Prod.fst hz1
      have hy1 := congrArg Prod.snd hz1
      apply Prod.ext <;> simp only [addPoint, scalePoint] at * <;> dsimp [f] at * <;> omega
    apply Drift.stableRank_injective_on_class hd hv
      (Drift.mem_classPhases.mpr ⟨hffi, hclass⟩)
      (Drift.mem_classPhases.mpr ⟨hi, Drift.SameClass.refl _ _⟩)
    exact hi2.2.trans hi1.2
  have hnfix : ∀ i, i < P → f i ≠ i := by
    intro i hi he
    obtain ⟨_, z, hz⟩ := Drift.mem_classPhases.mp (hspec i hi).1
    change addPoint (wordPos w i) (1, -1) = addPoint (wordPos w (f i)) (scalePoint (2, -2) z) at hz
    rw [he] at hz
    have hx := congrArg Prod.fst hz
    simp only [addPoint, scalePoint] at hx
    omega
  let q := f 0
  have hq : q < P := hf 0 hP
  have hqne : q ≠ 0 := hnfix 0 hP
  have hqq : (q+q)%P=0 := by
    have h1 := hshift q hq
    have h2 := hinvolution 0 hP
    change f q = 0 at h2
    change f q = (q+q)%P at h1
    exact h1.symm.trans h2
  have hhalf : q+q=P := involutive_shift_half hP hq hqne hqq
  have hcolor : ∀ i, i < P → w ((q+i)%P)=w i := by
    intro i hi
    have hc := DirectionTableTranslation.F_color hw hd hv hsym hi
    change w (f i) = w i at hc
    rw [hshift i hi] at hc
    exact hc
  have hr : RootWord.ReadPeriod q (repeatWord P w) := by
    intro n
    change w ((n+q)%P)=w (n%P)
    have hc := hcolor (n%P) (Nat.mod_lt _ hP)
    simpa only [Nat.add_comm q, Nat.mod_add_mod] using hc
  have hwr : ConsistentWord P (repeatWord P w) :=
    hw.congr (fun i hi => (repeatWord_prefix w hi).symm)
  have hprime : RootWord.Prime 2 := by
    constructor
    · omega
    · intro d hdvd
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
      have hne : d ≠ 0 := by intro he; subst d; simp at hdvd
      omega
  apply RootWord.prime_drift_minimal hwr hprime
    (by rw [repeatWord_drift]; exact hd) (show 0 < q by omega) hq
    (show q ∣ P from ⟨2, by omega⟩) hr


end LangtonsAnt.PersistA.TranslationShift
