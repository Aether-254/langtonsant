import LangtonsAnt

namespace LangtonsAnt.PersistA.ParityBand

structure Site where
  x : Int
  odd : Bool

def tail : List Site -> Int -> Bool
  | [], _ => false
  | s :: ss, lo => (if lo <= s.x then s.odd else false) ^^ tail ss lo

def band : List Site -> Int -> Int -> Bool
  | [], _, _ => false
  | s :: ss, lo, hi => (if lo <= s.x ∧ s.x < hi then s.odd else false) ^^ band ss lo hi

private theorem xor_shuffle (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem tail_split (ss : List Site) {lo hi : Int} (hle : lo <= hi) :
    tail ss lo = (band ss lo hi ^^ tail ss hi) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      have hh : (if lo <= s.x then s.odd else false) =
          ((if lo <= s.x ∧ s.x < hi then s.odd else false) ^^
          (if hi <= s.x then s.odd else false)) := by
        by_cases hlo : lo <= s.x
        · by_cases hhi : hi <= s.x
          · simp [hlo, hhi, show ¬s.x < hi by omega]
          · simp [hlo, hhi, show s.x < hi by omega]
        · simp [hlo, show ¬hi <= s.x by omega]
      simp only [tail, band, hh, ih]
      exact xor_shuffle _ _ _ _

theorem band_true_has_odd {ss : List Site} {lo hi : Int}
    (h : band ss lo hi = true) :
    ∃ s ∈ ss, lo <= s.x ∧ s.x < hi ∧ s.odd = true := by
  induction ss with
  | nil => simp [band] at h
  | cons s ss ih =>
      by_cases hpos : lo <= s.x ∧ s.x < hi
      · cases ho : s.odd with
        | false =>
            have ht : band ss lo hi = true := by simpa [band, hpos, ho] using h
            obtain ⟨q, hq, hdata⟩ := ih ht
            exact ⟨q, List.mem_cons_of_mem s hq, hdata⟩
        | true => exact ⟨s, by simp, hpos.1, hpos.2, ho⟩
      · have ht : band ss lo hi = true := by simpa [band, hpos] using h
        obtain ⟨q, hq, hdata⟩ := ih ht
        exact ⟨q, List.mem_cons_of_mem s hq, hdata⟩

theorem tail_true_has_odd {ss : List Site} {lo : Int}
    (h : tail ss lo = true) : ∃ s ∈ ss, lo <= s.x ∧ s.odd = true := by
  induction ss with
  | nil => simp [tail] at h
  | cons s ss ih =>
      by_cases hpos : lo <= s.x
      · cases ho : s.odd with
        | false =>
            have ht : tail ss lo = true := by simpa [tail, hpos, ho] using h
            obtain ⟨q, hq, hdata⟩ := ih ht
            exact ⟨q, List.mem_cons_of_mem s hq, hdata⟩
        | true => exact ⟨s, by simp, hpos, ho⟩
      · have ht : tail ss lo = true := by simpa [tail, hpos] using h
        obtain ⟨q, hq, hdata⟩ := ih ht
        exact ⟨q, List.mem_cons_of_mem s hq, hdata⟩

theorem different_tails_force_strict_interlacing {ss : List Site} {a b : Int}
    (hab : a < b) (hne : tail ss (a + 1) ≠ tail ss (b + 1))
    (hno : ∀ s ∈ ss, s.x ≠ b) :
    ∃ s ∈ ss, a < s.x ∧ s.x < b ∧ s.odd = true := by
  have hsplit := tail_split ss (lo := a + 1) (hi := b + 1) (by omega)
  have hb : band ss (a + 1) (b + 1) = true := by
    cases he : band ss (a + 1) (b + 1) with
    | false => simp only [he, Bool.false_xor] at hsplit; exact False.elim (hne hsplit)
    | true => rfl
  obtain ⟨s, hs, hlo, hhi, ho⟩ := band_true_has_odd hb
  have hn := hno s hs
  exact ⟨s, hs, by omega, by omega, ho⟩


end LangtonsAnt.PersistA.ParityBand
