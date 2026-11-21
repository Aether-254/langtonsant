import PeriodicWordEnumeration

/-!
# A fast consistency checker, proved equal to `checkConsistentWord`

`checkConsistentWord` recomputes `wordPos w n` from scratch for every lookup, so one word costs
about `P^3` steps.  `fastCheck` builds the path once into an array and is proved equal to
`checkConsistentWord`, so evaluating it (in particular with `native_decide`, in the separate
module `PeriodicWordNative`) still yields statements about `ConsistentWord`.
-/

namespace LangtonsAnt

/-- Extend `acc` (positions `0..n`) by `k` more steps, from pose `(p, d)` at step `n`. -/
def traceLoop (w : Nat -> Bool) : Nat -> Point -> Direction -> Nat -> Array Point ->
    Array Point × Direction
  | 0, _, d, _, acc => (acc, d)
  | k + 1, p, d, n, acc =>
    traceLoop w k (move p (turn (w n) d)) (turn (w n) d) (n + 1) (acc.push (move p (turn (w n) d)))

theorem traceLoop_spec (w : Nat -> Bool) (k : Nat) :
    forall (n : Nat) (acc : Array Point),
      acc.size = n + 1 ->
      (forall j, j <= n -> acc[j]? = some (wordPos w j)) ->
      (traceLoop w k (wordPos w n) (wordTrace w n).2 n acc).1.size = n + k + 1 ∧
      (forall j, j <= n + k ->
        (traceLoop w k (wordPos w n) (wordTrace w n).2 n acc).1[j]? = some (wordPos w j)) ∧
      (traceLoop w k (wordPos w n) (wordTrace w n).2 n acc).2 = (wordTrace w (n + k)).2 := by
  induction k with
  | zero =>
    intro n acc hs ha
    exact ⟨by simpa [traceLoop] using hs, fun j hj => by simpa [traceLoop] using ha j hj,
      by simp [traceLoop]⟩
  | succ k ih =>
    intro n acc hs ha
    have hstep : move (wordPos w n) (turn (w n) (wordTrace w n).2) = wordPos w (n + 1) := rfl
    have hdir : turn (w n) (wordTrace w n).2 = (wordTrace w (n + 1)).2 := rfl
    have hs' : (acc.push (wordPos w (n + 1))).size = n + 1 + 1 := by simp [hs]
    have ha' : forall j, j <= n + 1 ->
        (acc.push (wordPos w (n + 1)))[j]? = some (wordPos w j) := by
      intro j hj
      rw [Array.getElem?_push]
      by_cases he : j = acc.size
      · simp only [he, ite_true]
        rw [hs]
      · simp only [he, ite_false]
        exact ha j (by omega)
    have h := ih (n + 1) _ hs' ha'
    simp only [traceLoop, hdir]
    rw [show n + 1 + k = n + (k + 1) by omega] at h
    exact h

def traceArr (w : Nat -> Bool) (P : Nat) : Array Point × Direction :=
  traceLoop w P (0, 0) .north 0 #[(0, 0)]

theorem traceArr_spec (w : Nat -> Bool) (P : Nat) :
    (forall j, j <= P -> ((traceArr w P).1[j]?).getD (0, 0) = wordPos w j) ∧
      (traceArr w P).2 = (wordTrace w P).2 := by
  have h := traceLoop_spec w P 0 #[(0, 0)] (by simp) (by
    intro j hj
    have : j = 0 := by omega
    subst this
    rfl)
  have hzero : wordPos w 0 = (0, 0) := rfl
  have hdz : (wordTrace w 0).2 = .north := rfl
  rw [hzero, hdz, Nat.zero_add] at h
  refine ⟨fun j hj => ?_, h.2.2⟩
  unfold traceArr
  rw [h.2.1 j hj]
  rfl

theorem all_congr_mem {α : Type} {l : List α} {f g : α -> Bool} (h : forall a, a ∈ l -> f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x (by simp), ih (fun a ha => h a (by simp [ha]))]

/-- Same test as `checkConsistentWord`, with positions read from the precomputed array. -/
def fastCheck (P : Nat) (w : Nat -> Bool) : Bool :=
  let tr := traceArr w P
  let pos := fun n => (tr.1[n]?).getD (0, 0)
  let v := pos P
  decide (tr.2 = .north) && decide (v ≠ (0, 0)) &&
    (List.range P).all (fun i => w i ==
      decide (((List.range P).filter (checkEarlierPhase pos v i)).length % 2 = 1))

theorem fastCheck_eq (P : Nat) (w : Nat -> Bool) : fastCheck P w = checkConsistentWord P w := by
  have hs := traceArr_spec w P
  have hv : ((traceArr w P).1[P]?).getD (0, 0) = wordDrift P w := hs.1 P (Nat.le_refl P)
  have hpos : forall n, n < P -> ((traceArr w P).1[n]?).getD (0, 0) = wordPos w n :=
    fun n hn => hs.1 n (by omega)
  unfold fastCheck checkConsistentWord priorPhases
  simp only [hs.2, hv]
  congr 1
  apply all_congr_mem
  intro i hi
  have hi' := List.mem_range.mp hi
  have hf : List.filter (checkEarlierPhase (fun n => ((traceArr w P).1[n]?).getD (0, 0))
      (wordDrift P w) i) (List.range P) =
      List.filter (checkEarlierPhase (wordPos w) (wordDrift P w) i) (List.range P) := by
    apply List.filter_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    unfold checkEarlierPhase
    simp only [hpos i hi', hpos j hj']
  rw [hf]

/-- Tail-recursive scan of the encodings `start, ..., start + n - 1`. -/
def fastScan (P : Nat) : Nat -> Nat -> Bool
  | 0, _ => true
  | n + 1, c => if fastCheck P (fun i => c.testBit i) then false else fastScan P n (c + 1)

theorem fastScan_sound {P : Nat} : forall (n start : Nat), fastScan P n start = true ->
    forall c, start <= c -> c < start + n -> checkConsistentWord P (fun i => c.testBit i) = false := by
  intro n
  induction n with
  | zero => intro start _ c h1 h2; omega
  | succ n ih =>
    intro start h c h1 h2
    simp only [fastScan] at h
    by_cases hf : fastCheck P (fun i => start.testBit i) = true
    · simp [hf] at h
    · simp only [hf, Bool.false_eq_true, ite_false] at h
      by_cases hc : c = start
      · subst hc
        rw [← fastCheck_eq]
        simpa using hf
      · exact ih (start + 1) h c (by omega) (by omega)

theorem checkNoWords_of_fastScan {P : Nat} (h : fastScan P (2 ^ P) 0 = true) :
    checkNoWords P = true := by
  apply List.all_eq_true.mpr
  intro c hc
  have hlt := List.mem_range.mp hc
  simp [fastScan_sound (2 ^ P) 0 h c (Nat.zero_le c) (by omega)]

/-- Combine independent block scans (each its own module, so they can run in parallel). -/
theorem checkNoWords_of_fastBlocks {P width blocks : Nat} (hw : 0 < width)
    (hsize : 2 ^ P <= width * blocks)
    (h : forall k, k < blocks -> fastScan P width (width * k) = true) :
    checkNoWords P = true := by
  apply List.all_eq_true.mpr
  intro c hc
  have hlt : c < 2 ^ P := List.mem_range.mp hc
  have hk : c / width < blocks := by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [Nat.mul_comm] using Nat.lt_of_lt_of_le hlt hsize
  have hh := Nat.div_add_mod c width
  have hm := Nat.mod_lt c hw
  have he := fastScan_sound width (width * (c / width)) (h (c / width) hk) c (by omega) (by omega)
  simp [he]

end LangtonsAnt
