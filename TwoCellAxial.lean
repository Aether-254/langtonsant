import PortInversion
import PeriodicGrowthResidue

/-!
# Two-cell axial drift exclusion and mod-8 constraints (`TwoCellAxial.lean`)

Formalizes Batch 3 (L15, L17–L20, L27) of `research/growth-blueprint-2026-11-22.md` purely in the
Lean kernel (no `sorry`, no `axiom`, no `native_decide`).

## Contents

1. List-level `PortInversion` / `pairCross` / `succ`-cycle parity helpers.
2. **L15**: Even-step four-mod square-sum identity for drift `(2, 0)`.
3. **L17**: Quotient-graph `(Q_y, C_y)` geometry, `rankList` ordering, cut balance, and local
   left-turn stable-rank sum.
4. **L18**: Quotient-graph instantiation of block inversion decomposition, edge-block crossing
   parity `E`, and the kinematic rank identity `K ≡ 1 + P / 4 (mod 2)`.
5. **L19–L20 / L27**: Exclusion of `g = 4`, Ke's Theorem B (`P % 8 = 4 ∧ g % 8 = 0`) for `(2, 0)`
   and all four two-cell axial drifts, in both word and periodic-tail orbit forms.
-/

namespace LangtonsAnt

namespace TwoCellAxial

/-! ## 1. Pure list, `PortInversion`, and `succ`-cycle parity helpers -/

private theorem nat_sum_append (xs ys : List Nat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.cons_append, List.sum_cons, ih]; omega

private theorem int_sum_append (xs ys : List Int) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.cons_append, List.sum_cons, ih]; omega

private theorem int_sum_map_congr {α : Type} {f g : α → Int} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, h x (by simp),
      ih (fun y hy => h y (by simp [hy]))]

private theorem nat_sum_map_congr {α : Type} {f g : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, h x (by simp),
      ih (fun y hy => h y (by simp [hy]))]

private theorem int_sum_map_add {α : Type} (f g : α → Int) (xs : List α) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem nat_sum_map_add {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem nat_sum_map_mod_congr {α : Type} {f g : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x % 2 = g x % 2) :
    (xs.map f).sum % 2 = (xs.map g).sum % 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem listInv_map_succ (xs : List Nat) :
    PortInversion.listInv (xs.map (· + 1)) = PortInversion.listInv xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, PortInversion.listInv_cons, PortInversion.listInv_cons, ih]
    have hf : ((xs.map (· + 1)).filter (fun y => y < x + 1)).length =
        (xs.filter (fun y => y < x)).length := by
      rw [List.filter_map, List.length_map]
      congr 1
    rw [hf]

private theorem crossInv_map_succ (as bs : List Nat) :
    PortInversion.crossInv (as.map (· + 1)) (bs.map (· + 1)) = PortInversion.crossInv as bs := by
  induction as with
  | nil => rfl
  | cons x as ih =>
    rw [List.map_cons, PortInversion.crossInv_cons, PortInversion.crossInv_cons, ih]
    have hf : ((bs.map (· + 1)).filter (fun y => y < x + 1)).length =
        (bs.filter (fun y => y < x)).length := by
      rw [List.filter_map, List.length_map]
      congr 1
    rw [hf]

/-- Mapping the single cycle `succ P` across any permutation of `range P` flips inversion parity by
`(P - 1) % 2` (hence by `1` whenever `P` is a positive even integer). -/
theorem listInv_map_succ_parity {P : Nat} {xs : List Nat}
    (hP : 0 < P) (hperm : xs.Perm (List.range P)) :
    (PortInversion.listInv (xs.map (Drift.succ P)) + PortInversion.listInv xs) % 2 =
      (P - 1) % 2 := by
  have hnd : xs.Nodup := hperm.symm.nodup List.nodup_range
  have hmem : P - 1 ∈ xs := hperm.mem_iff.mpr (List.mem_range.mpr (by omega))
  obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hmem
  have hlen : pre.length + 1 + suf.length = P := by
    have hl := hperm.length_eq
    simp only [List.length_append, List.length_cons, List.length_range] at hl
    omega
  have hlt_pre : ∀ x ∈ pre, x < P - 1 := by
    intro x hx
    have hxP : x < P := List.mem_range.mp (hperm.mem_iff.mp (List.mem_append_left _ hx))
    have hne : x ≠ P - 1 := by
      intro he
      subst he
      have hnd' := (List.nodup_append.mp hnd).2.2
      exact hnd' (P - 1) hx (P - 1) (List.mem_cons_self) rfl
    omega
  have hlt_suf : ∀ y ∈ suf, y < P - 1 := by
    intro y hy
    have hyP : y < P := List.mem_range.mp
      (hperm.mem_iff.mp (List.mem_append_right _ (List.mem_cons_of_mem _ hy)))
    have hne : y ≠ P - 1 := by
      intro he
      subst he
      have hnd' := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
      exact hnd' hy
    omega
  have hmap_pre : pre.map (Drift.succ P) = pre.map (· + 1) := by
    apply List.map_congr_left
    intro x hx
    have hxlt := hlt_pre x hx
    show (x + 1) % P = x + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hmap_suf : suf.map (Drift.succ P) = suf.map (· + 1) := by
    apply List.map_congr_left
    intro y hy
    have hylt := hlt_suf y hy
    show (y + 1) % P = y + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hsucc_last : Drift.succ P (P - 1) = 0 := by
    show (P - 1 + 1) % P = 0
    rw [show P - 1 + 1 = P by omega, Nat.mod_self]
  have hxs_inv : PortInversion.listInv (pre ++ (P - 1) :: suf) =
      PortInversion.listInv pre + suf.length + PortInversion.listInv suf +
        PortInversion.crossInv pre suf := by
    rw [PortInversion.listInv_append, PortInversion.listInv_cons, PortInversion.crossInv_cons_right,
      PortInversion.crossInv_singleton_right]
    have h1 : (suf.filter (fun y => decide (y < P - 1))).length = suf.length := by
      rw [List.filter_eq_self.mpr (fun y hy => decide_eq_true (hlt_suf y hy))]
    have h2 : (pre.filter (fun u => decide (P - 1 < u))).length = 0 := by
      rw [List.filter_eq_nil_iff.mpr (fun x hx => by simp; have := hlt_pre x hx; omega)]
      rfl
    rw [h1, h2]
    omega
  have hmap_inv : PortInversion.listInv ((pre ++ (P - 1) :: suf).map (Drift.succ P)) =
      PortInversion.listInv pre + PortInversion.listInv suf + pre.length +
        PortInversion.crossInv pre suf := by
    rw [List.map_append, List.map_cons, hmap_pre, hmap_suf, hsucc_last,
      PortInversion.listInv_append, PortInversion.listInv_cons, PortInversion.crossInv_cons_right,
      PortInversion.crossInv_singleton_right, listInv_map_succ, listInv_map_succ, crossInv_map_succ]
    have h1 : ((suf.map (· + 1)).filter (fun y => decide (y < 0))).length = 0 := by
      rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]
      rfl
    have h2 : ((pre.map (· + 1)).filter (fun u => decide (0 < u))).length = pre.length := by
      rw [List.filter_eq_self.mpr (fun u hu => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hu
        simp), List.length_map]
    rw [h1, h2]
    omega
  rw [hxs_inv, hmap_inv]
  omega

theorem crossInv_perm_right (a : List Nat) {b1 b2 : List Nat} (hp : b1.Perm b2) :
    PortInversion.crossInv a b1 = PortInversion.crossInv a b2 := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    rw [PortInversion.crossInv_cons, PortInversion.crossInv_cons,
      (hp.filter (fun y => decide (y < x))).length_eq, ih]

theorem crossInv_perm_left {a1 a2 : List Nat} (hp : a1.Perm a2) (b : List Nat) :
    PortInversion.crossInv a1 b = PortInversion.crossInv a2 b := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    rw [PortInversion.crossInv_cons, PortInversion.crossInv_cons, ih]
  | swap x y l =>
    rw [PortInversion.crossInv_cons, PortInversion.crossInv_cons,
      PortInversion.crossInv_cons, PortInversion.crossInv_cons]
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem crossInv_add_symm_of_disjoint {a b : List Nat}
    (hdisj : ∀ x ∈ a, ∀ y ∈ b, x ≠ y) :
    PortInversion.crossInv a b + PortInversion.crossInv b a = a.length * b.length := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [PortInversion.crossInv_cons, PortInversion.crossInv_cons_right,
      PortInversion.crossInv_singleton_right]
    have hxnot : x ∉ b := fun hmem => hdisj x List.mem_cons_self x hmem rfl
    have htri := PortInversion.filter_lt_add_filter_gt x b hxnot
    have ih' := ih (fun u hu y hy => hdisj u (List.mem_cons_of_mem x hu) y hy)
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem pairCross_append (L1 L2 : List (List Nat)) :
    PortInversion.pairCross (L1 ++ L2) =
      PortInversion.pairCross L1 + PortInversion.pairCross L2 +
        PortInversion.crossInv L1.flatten L2.flatten := by
  induction L1 with
  | nil => simp [PortInversion.pairCross]
  | cons b L1 ih =>
    simp only [List.cons_append, PortInversion.pairCross, List.flatten_append, List.flatten_cons,
      PortInversion.crossInv_append_right, PortInversion.crossInv_append_left, ih]
    omega

theorem pairCross_cons_nil (L : List (List Nat)) :
    PortInversion.pairCross ([] :: L) = PortInversion.pairCross L := by
  simp [PortInversion.pairCross]

theorem pairCross_append_nil (L : List (List Nat)) :
    PortInversion.pairCross (L ++ [[]]) = PortInversion.pairCross L := by
  rw [pairCross_append]
  simp [PortInversion.pairCross]

theorem pairCross_pull_to_front_mod (pre suf : List (List Nat)) (a : List Nat)
    (hdisj : ∀ x ∈ pre.flatten, ∀ y ∈ a, x ≠ y) :
    (PortInversion.pairCross (pre ++ a :: suf) +
      PortInversion.pairCross (a :: (pre ++ suf))) % 2 =
      (pre.flatten.length * a.length) % 2 := by
  have h1 : PortInversion.pairCross (pre ++ a :: suf) =
      PortInversion.pairCross pre + PortInversion.crossInv a suf.flatten +
      PortInversion.pairCross suf + PortInversion.crossInv pre.flatten a +
      PortInversion.crossInv pre.flatten suf.flatten := by
    rw [pairCross_append, PortInversion.pairCross, List.flatten_cons,
      PortInversion.crossInv_append_right]
    omega
  have h2 : PortInversion.pairCross (a :: (pre ++ suf)) =
      PortInversion.crossInv a pre.flatten + PortInversion.crossInv a suf.flatten +
      PortInversion.pairCross pre + PortInversion.pairCross suf +
      PortInversion.crossInv pre.flatten suf.flatten := by
    rw [PortInversion.pairCross, List.flatten_append, PortInversion.crossInv_append_right,
      pairCross_append]
    omega
  have hsym := crossInv_add_symm_of_disjoint hdisj
  rw [h1, h2]
  omega

theorem pairCross_strip_prefix_mod (pre L1 L2 : List (List Nat))
    (hp : L1.flatten.Perm L2.flatten) :
    (PortInversion.pairCross (pre ++ L1) + PortInversion.pairCross (pre ++ L2)) % 2 =
      (PortInversion.pairCross L1 + PortInversion.pairCross L2) % 2 := by
  rw [pairCross_append, pairCross_append, crossInv_perm_right pre.flatten hp]
  omega

theorem listInv_flatten_perm_blocks_mod {L1 L2 : List (List Nat)} (hp : L1.Perm L2) :
    (PortInversion.listInv L1.flatten + PortInversion.listInv L2.flatten) % 2 =
      (PortInversion.pairCross L1 + PortInversion.pairCross L2) % 2 := by
  rw [PortInversion.listInv_flatten, PortInversion.listInv_flatten,
    PortInversion.perm_sum (hp.map PortInversion.listInv)]
  omega

theorem listInv_flatten_map_stablePart_mod (L : List (List Nat))
    (hn : ∀ b ∈ L, b.Nodup) (k : Nat → Bool) :
    (PortInversion.listInv ((L.map (PortInversion.stablePart k)).flatten) +
      PortInversion.listInv L.flatten) % 2 =
      (L.map (fun b => PortInversion.wordInv (b.map k))).sum % 2 := by
  have hdec := PortInversion.block_decomposition L L (List.Perm.refl L) hn (fun _ => false) k
  have hsp : ∀ b : List Nat,
      PortInversion.stablePart (fun _ => false) (PortInversion.stablePart k b) =
        PortInversion.stablePart k b := by
    intro b
    unfold PortInversion.stablePart
    simp
  have hmap : L.map (fun b => PortInversion.stablePart (fun _ => false) (PortInversion.stablePart k b)) =
      L.map (PortInversion.stablePart k) :=
    List.map_congr_left (fun b _ => hsp b)
  have hw0 : ∀ l : List Nat, PortInversion.wordInv (l.map (fun _ => false)) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons _ l ih => exact ih
  have hsum0 : (L.map (fun b => PortInversion.wordInv ((PortInversion.stablePart k b).map (fun _ => false)))).sum = 0 := by
    have h0 : ∀ xs : List (List Nat), (xs.map (fun _ => (0 : Nat))).sum = 0 := by
      intro xs; induction xs with | nil => rfl | cons _ xs ih => simp [ih]
    rw [nat_sum_map_congr (fun b _ => hw0 _)]
    exact h0 L
  rw [hmap, hsum0] at hdec
  omega

theorem eq_of_perm_pairwise_lt {α : Type} (f : α → Nat) :
    ∀ {xs ys : List α}, xs.Perm ys →
      xs.Pairwise (fun a b => f a < f b) →
      ys.Pairwise (fun a b => f a < f b) → xs = ys
  | [], ys, hp, _, _ => (List.perm_nil.mp hp.symm).symm
  | x :: xs, [], hp, _, _ => absurd (List.perm_nil.mp hp) (by simp)
  | x :: xs, y :: ys, hp, hpx, hpy => by
    obtain ⟨hx, hpx'⟩ := List.pairwise_cons.mp hpx
    obtain ⟨hy, hpy'⟩ := List.pairwise_cons.mp hpy
    have hxy : x = y := by
      have hx_in : x ∈ y :: ys := hp.mem_iff.mp List.mem_cons_self
      have hy_in : y ∈ x :: xs := hp.symm.mem_iff.mp List.mem_cons_self
      rcases List.mem_cons.mp hx_in with rfl | hx_ys
      · rfl
      · rcases List.mem_cons.mp hy_in with rfl | hy_xs
        · rfl
        · have h1 := hy x hx_ys
          have h2 := hx y hy_xs
          omega
    subst hxy
    congr 1
    exact eq_of_perm_pairwise_lt f (List.Perm.cons_inv hp) hpx' hpy'

private theorem countTrue_append_singleton (l : List Bool) (b : Bool) :
    PortInversion.countTrue (l ++ [b]) =
      PortInversion.countTrue l + if b then 1 else 0 := by
  induction l with
  | nil => cases b <;> rfl
  | cons d l ih =>
    cases d <;> simp only [List.cons_append, PortInversion.countTrue] at ih ⊢ <;> omega

theorem rankSum_append_singleton (α : List Bool) (b : Bool) :
    PortInversion.rankSum (α ++ [b]) =
      PortInversion.rankSum α + if b then α.length else 0 := by
  induction α with
  | nil => cases b <;> rfl
  | cons c α ih =>
    have hct := countTrue_append_singleton α b
    simp only [List.cons_append, PortInversion.rankSum, ih, hct, List.length_cons]
    cases b <;> simp <;> omega

theorem rankSum_map_range (n : Nat) (f : Nat → Bool) :
    PortInversion.rankSum ((List.range n).map f) = ((List.range n).filter f).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, rankSum_append_singleton, ih,
      List.filter_append, nat_sum_append, List.length_map, List.length_range]
    cases hf : f n <;> simp [hf]

theorem sum_range_eq_pairCount (n : Nat) :
    (List.range n).sum = PortInversion.pairCount n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, nat_sum_append, ih, List.sum_singleton, PortInversion.pairCount_succ]

theorem pairCount_add (a b : Nat) :
    PortInversion.pairCount (a + b) =
      PortInversion.pairCount a + PortInversion.pairCount b + a * b := by
  induction b with
  | zero => simp [PortInversion.pairCount]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, PortInversion.pairCount_succ,
      PortInversion.pairCount_succ, ih, Nat.mul_succ]
    omega

/-! ## 2. L15: Even-step four-mod square-sum identity -/

/-- Horizontal step sign: `+1` east, `-1` west, `0` vertical. -/
def uSign : Direction → Int
  | .east => 1
  | .west => -1
  | .north | .south => 0

/-- Vertical step sign: `+1` north, `-1` south, `0` horizontal. -/
def vSign : Direction → Int
  | .north => 1
  | .south => -1
  | .east | .west => 0

theorem move_fst_eq_uSign (p : Point) (d : Direction) :
    (move p d).1 = p.1 + uSign d := by
  cases d <;> simp [move, uSign] <;> omega

theorem move_snd_eq_vSign (p : Point) (d : Direction) :
    (move p d).2 = p.2 + vSign d := by
  cases d <;> simp [move, vSign] <;> omega

theorem inDir_vertical_of_even (w : Nat → Bool) {i : Nat} (hi : i % 2 = 0) :
    Drift.inDir w i = .north ∨ Drift.inDir w i = .south := by
  have hax := wordTrace_axis w i
  change (Drift.inDir w i).horizontal = decide (i % 2 = 1) at hax
  have hne : decide (i % 2 = 1) = false := decide_eq_false (by omega)
  rw [hne] at hax
  cases hd : Drift.inDir w i <;> simp [hd, Direction.horizontal] at hax ⊢

theorem inDir_horizontal_of_odd (w : Nat → Bool) {i : Nat} (hi : i % 2 = 1) :
    Drift.inDir w i = .east ∨ Drift.inDir w i = .west := by
  have hax := wordTrace_axis w i
  change (Drift.inDir w i).horizontal = decide (i % 2 = 1) at hax
  have ht : decide (i % 2 = 1) = true := decide_eq_true hi
  rw [ht] at hax
  cases hd : Drift.inDir w i <;> simp [hd, Direction.horizontal] at hax ⊢

theorem outDir_horizontal_of_even (w : Nat → Bool) {i : Nat} (hi : i % 2 = 0) :
    Drift.outDir w i = .east ∨ Drift.outDir w i = .west := by
  rcases inDir_vertical_of_even w hi with h | h <;> cases hb : w i <;>
    simp [Drift.outDir, UnitDiagonalMatching.outDir, h, hb, turn, Direction.left, Direction.right]

theorem outDir_vertical_of_odd (w : Nat → Bool) {i : Nat} (hi : i % 2 = 1) :
    Drift.outDir w i = .north ∨ Drift.outDir w i = .south := by
  rcases inDir_horizontal_of_odd w hi with h | h <;> cases hb : w i <;>
    simp [Drift.outDir, UnitDiagonalMatching.outDir, h, hb, turn, Direction.left, Direction.right]

theorem even_step_signs (w : Nat → Bool) (j : Nat) :
    (uSign (Drift.outDir w (2 * j)) = 1 ∨ uSign (Drift.outDir w (2 * j)) = -1) ∧
    (vSign (Drift.inDir w (2 * j)) = 1 ∨ vSign (Drift.inDir w (2 * j)) = -1) ∧
    turnSign (w (2 * j)) = uSign (Drift.outDir w (2 * j)) * vSign (Drift.inDir w (2 * j)) := by
  rcases inDir_vertical_of_even w (by omega : (2 * j) % 2 = 0) with hd | hd <;>
    cases hb : w (2 * j) <;>
    simp [Drift.outDir, UnitDiagonalMatching.outDir, hd, hb, turn, turnSign,
      Direction.left, Direction.right, uSign, vSign]

theorem wordPos_even_fst_eq_sum_u (w : Nat → Bool) (m : Nat) :
    (wordPos w (2 * m)).1 =
      ((List.range m).map (fun j => uSign (Drift.outDir w (2 * j)))).sum := by
  induction m with
  | zero => simp [wordPos, wordTrace]
  | succ m ih =>
    rw [List.range_succ, List.map_append, int_sum_append, List.map_singleton, List.sum_singleton,
      ← ih]
    have hstep1 : (wordPos w (2 * m + 1)).1 =
        (wordPos w (2 * m)).1 + uSign (Drift.outDir w (2 * m)) :=
      move_fst_eq_uSign (wordPos w (2 * m)) (Drift.outDir w (2 * m))
    have hstep2 : (wordPos w (2 * (m + 1))).1 =
        (wordPos w (2 * m + 1)).1 + uSign (Drift.outDir w (2 * m + 1)) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
      exact move_fst_eq_uSign (wordPos w (2 * m + 1)) (Drift.outDir w (2 * m + 1))
    have hodd : uSign (Drift.outDir w (2 * m + 1)) = 0 := by
      rcases outDir_vertical_of_odd w (by omega : (2 * m + 1) % 2 = 1) with h | h <;>
        simp [h, uSign]
    omega

theorem wordPos_even_snd_eq_sum_v_shifted (w : Nat → Bool) (m : Nat) :
    (wordPos w (2 * m)).2 =
      ((List.range m).map (fun j => vSign (Drift.inDir w (2 * (j + 1))))).sum := by
  induction m with
  | zero => simp [wordPos, wordTrace]
  | succ m ih =>
    rw [List.range_succ, List.map_append, int_sum_append, List.map_singleton, List.sum_singleton,
      ← ih]
    have hstep1 : (wordPos w (2 * m + 1)).2 =
        (wordPos w (2 * m)).2 + vSign (Drift.outDir w (2 * m)) :=
      move_snd_eq_vSign (wordPos w (2 * m)) (Drift.outDir w (2 * m))
    have hstep2 : (wordPos w (2 * (m + 1))).2 =
        (wordPos w (2 * m + 1)).2 + vSign (Drift.outDir w (2 * m + 1)) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
      exact move_snd_eq_vSign (wordPos w (2 * m + 1)) (Drift.outDir w (2 * m + 1))
    have heven : vSign (Drift.outDir w (2 * m)) = 0 := by
      rcases outDir_horizontal_of_even w (by omega : (2 * m) % 2 = 0) with h | h <;>
        simp [h, vSign]
    have hdir : Drift.inDir w (2 * (m + 1)) = Drift.outDir w (2 * m + 1) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
      rfl
    rw [hdir]
    omega

private theorem int_sum_shift_eq {f : Nat → Int} (m : Nat) (he : f m = f 0) :
    ((List.range m).map (fun j => f (j + 1))).sum = ((List.range m).map f).sum := by
  have hgen : ∀ n, ((List.range n).map (fun j => f (j + 1))).sum + f 0 =
      ((List.range n).map f).sum + f n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append, int_sum_append, int_sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      omega
  have h := hgen m
  omega

theorem wordPos_even_snd_eq_sum_v {w : Nat → Bool} {m : Nat}
    (hh : (wordTrace w (2 * m)).2 = .north) :
    (wordPos w (2 * m)).2 =
      ((List.range m).map (fun j => vSign (Drift.inDir w (2 * j)))).sum := by
  rw [wordPos_even_snd_eq_sum_v_shifted]
  apply int_sum_shift_eq (f := fun j => vSign (Drift.inDir w (2 * j))) m
  change vSign (wordTrace w (2 * m)).2 = vSign (wordTrace w 0).2
  rw [hh]
  rfl

private theorem sum_range_two_mul_even_indicator (m : Nat) (f : Nat → Int) :
    ((List.range (2 * m)).map (fun i => (if i % 2 = 0 then (1 : Int) else 0) * f i)).sum =
      ((List.range m).map (fun j => f (2 * j))).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, List.range_succ, List.range_succ,
      List.map_append, List.map_append, int_sum_append, int_sum_append, ih,
      List.range_succ, List.map_append, int_sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have h0 : (2 * m) % 2 = 0 := by omega
    simp [h0]

theorem checkerSign_wordPos_eq_one_iff (w : Nat → Bool) (i : Nat) :
    checkerSign (wordPos w i) = 1 ↔ i % 2 = 0 := by
  have hp := wordPos_sum_parity w i
  unfold checkerSign
  split <;> omega

private theorem int_sum_map_indicator_eq_filter_len {α : Type} (p : α → Bool) (xs : List α) :
    (xs.map (fun x => if p x then (1 : Int) else 0)).sum = ((xs.filter p).length : Int) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x <;> simp [hpx, ih] <;> omega

/-- For a consistent word with drift `(2, 0)`, the sum of `turnSign (w (2*j))` over the `P / 2`
even steps equals `wordGrowth P w / 2`. -/
theorem drift_two_zero_even_turnSign_sum {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, 0)) :
    ((List.range (P / 2)).map (fun j => turnSign (w (2 * j)))).sum =
      ((wordGrowth P w / 2 : Nat) : Int) := by
  have hP2 : 2 * (P / 2) = P := by have := h.even; omega
  have hweight := h.sum_weighted_turnSign
    (fun i => if checkerSign (wordPos w i) = 1 then (1 : Int) else 0)
    (fun i j _ _ hsc => by rw [h.checkerSign_sameClass hsc])
  have hlhs :
      ((List.range P).map
        (fun i => (if checkerSign (wordPos w i) = 1 then (1 : Int) else 0) * turnSign (w i))).sum =
      ((List.range (P / 2)).map (fun j => turnSign (w (2 * j)))).sum := by
    have h0 := sum_range_two_mul_even_indicator (P / 2) (fun i => turnSign (w i))
    rw [hP2] at h0
    rw [← h0]
    apply int_sum_map_congr
    intro i _
    by_cases hi : i % 2 = 0
    · simp [hi, (checkerSign_wordPos_eq_one_iff w i).mpr hi]
    · have hne : checkerSign (wordPos w i) ≠ 1 := fun hc =>
        hi ((checkerSign_wordPos_eq_one_iff w i).mp hc)
      simp [hi, hne]
  have hrhs :
      ((oddClassReps P w).map
        (fun i => if checkerSign (wordPos w i) = 1 then (1 : Int) else 0)).sum =
      ((wordGrowth P w / 2 : Nat) : Int) := by
    have h1 := int_sum_map_indicator_eq_filter_len
      (fun i => decide (checkerSign (wordPos w i) = 1)) (oddClassReps P w)
    have h2 : ((oddClassReps P w).map
        (fun i => if checkerSign (wordPos w i) = 1 then (1 : Int) else 0)).sum =
      ((oddClassReps P w).map
        (fun i => if decide (checkerSign (wordPos w i) = 1) then (1 : Int) else 0)).sum := by
      apply int_sum_map_congr
      intro i _
      by_cases hc : checkerSign (wordPos w i) = 1 <;> simp [hc]
    rw [h2, h1, (h.drift_two_zero_checker_counts hd).1]
  rw [hlhs, hrhs] at hweight
  exact hweight

private theorem int_sum_mod_four_zero {α : Type} {f : α → Int} {xs : List α}
    (h : ∀ x ∈ xs, f x % 4 = 0) :
    (xs.map f).sum % 4 = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem int_sum_ones (m : Nat) :
    ((List.range m).map (fun _ => (1 : Int))).sum = (m : Int) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, int_sum_append, ih]
    simp only [List.map_singleton, List.sum_singleton]
    omega

/-- **L15 (even-step four-mod square-sum identity):** For any consistent word with drift `(2, 0)`,
pairing the `M = P / 2` even steps yields `(P / 2 + 2 + g / 2) % 4 = 0`. -/
theorem drift_two_zero_even_step_mod_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, 0)) :
    (P / 2 + 2 + wordGrowth P w / 2) % 4 = 0 := by
  let M := P / 2
  have hP2 : 2 * M = P := by have := h.even; omega
  have hhM : (wordTrace w (2 * M)).2 = .north := by rw [hP2]; exact h.1
  have hu : ((List.range M).map (fun j => uSign (Drift.outDir w (2 * j)))).sum = 2 := by
    rw [← wordPos_even_fst_eq_sum_u, hP2]
    change (wordDrift P w).1 = 2
    rw [hd]
  have hv : ((List.range M).map (fun j => vSign (Drift.inDir w (2 * j)))).sum = 0 := by
    rw [← wordPos_even_snd_eq_sum_v hhM, hP2]
    change (wordDrift P w).2 = 0
    rw [hd]
  have huv : ((List.range M).map
      (fun j => uSign (Drift.outDir w (2 * j)) * vSign (Drift.inDir w (2 * j)))).sum =
      ((wordGrowth P w / 2 : Nat) : Int) := by
    rw [← drift_two_zero_even_turnSign_sum h hd]
    apply int_sum_map_congr
    intro j _
    exact (even_step_signs w j).2.2.symm
  have hsq : ((List.range M).map (fun j =>
      (1 + uSign (Drift.outDir w (2 * j))) * (1 + vSign (Drift.inDir w (2 * j))))).sum % 4 = 0 := by
    apply int_sum_mod_four_zero
    intro j _
    obtain ⟨hu1, hv1, _⟩ := even_step_signs w j
    rcases hu1 with hu1 | hu1 <;> rcases hv1 with hv1 | hv1 <;> simp [hu1, hv1]
  have hexp : ((List.range M).map (fun j =>
      (1 + uSign (Drift.outDir w (2 * j))) * (1 + vSign (Drift.inDir w (2 * j))))).sum =
      (M : Int) + 2 + ((wordGrowth P w / 2 : Nat) : Int) := by
    have hpt : ((List.range M).map (fun j =>
        (1 + uSign (Drift.outDir w (2 * j))) * (1 + vSign (Drift.inDir w (2 * j))))).sum =
        ((List.range M).map (fun j =>
          ((1 : Int) + uSign (Drift.outDir w (2 * j))) +
            (vSign (Drift.inDir w (2 * j)) +
              uSign (Drift.outDir w (2 * j)) * vSign (Drift.inDir w (2 * j))))).sum := by
      apply int_sum_map_congr
      intro j _
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.one_mul, Int.mul_one]
      omega
    rw [hpt, int_sum_map_add, int_sum_map_add, int_sum_map_add, int_sum_ones, hu, hv, huv]
    omega
  rw [hexp] at hsq
  omega

/-! ## 3. L17: Quotient-graph `(Q_y, C_y)` geometry, `rankList`, cut balance, and local rank sum -/

/-- Canonical representative of the vertical-entry class `Q_y` on row `y` (even `x + y`). -/
def qRep (y : Int) : Point := (y % 2, y)

/-- Canonical representative of the horizontal-entry class `C_y` on row `y` (odd `x + y`). -/
def cRep (y : Int) : Point := (1 - y % 2, y)

theorem drift_two_zero_ne_zero : ((2 : Int), (0 : Int)) ≠ (0, 0) := by
  decide

theorem sameClass_two_zero_iff (p q : Point) :
    Drift.SameClass (2, 0) p q ↔ p.2 = q.2 ∧ p.1 % 2 = q.1 % 2 := by
  constructor
  · rintro ⟨z, hq⟩
    have hx := congrArg Prod.fst hq
    have hy := congrArg Prod.snd hq
    simp only [addPoint, scalePoint] at hx hy
    omega
  · rintro ⟨hy, hx⟩
    refine ⟨(q.1 - p.1) / 2, ?_⟩
    apply Prod.ext <;> simp only [addPoint, scalePoint] <;> omega

theorem sameClass_qRep_iff (p : Point) (y : Int) :
    Drift.SameClass (2, 0) p (qRep y) ↔ p.2 = y ∧ (p.1 + p.2) % 2 = 0 := by
  rw [sameClass_two_zero_iff]
  simp only [qRep]
  omega

theorem sameClass_cRep_iff (p : Point) (y : Int) :
    Drift.SameClass (2, 0) p (cRep y) ↔ p.2 = y ∧ (p.1 + p.2) % 2 = 1 := by
  rw [sameClass_two_zero_iff]
  simp only [cRep]
  omega

theorem sameClass_move_qRep_west (y : Int) :
    Drift.SameClass (2, 0) (move (qRep y) .west) (cRep y) := by
  rw [sameClass_cRep_iff]
  simp [qRep, move]
  omega

theorem sameClass_move_qRep_east (y : Int) :
    Drift.SameClass (2, 0) (move (qRep y) .east) (cRep y) := by
  rw [sameClass_cRep_iff]
  simp [qRep, move]
  omega

theorem sameClass_move_cRep_south (y : Int) :
    Drift.SameClass (2, 0) (move (cRep y) .south) (qRep (y - 1)) := by
  rw [sameClass_qRep_iff]
  simp [cRep, move]
  omega

theorem sameClass_move_cRep_north (y : Int) :
    Drift.SameClass (2, 0) (move (cRep y) .north) (qRep (y + 1)) := by
  rw [sameClass_qRep_iff]
  simp [cRep, move]
  omega

/-! ### Rank-ordered class lists (`rankList`) -/

/-- The unique phase of stable rank `r` in `Drift.classPhases v P w c` (or `0` out of range). -/
def rankPhase (v c : Point) (P : Nat) (w : Nat → Bool) (r : Nat) : Nat :=
  ((Drift.classPhases v P w c).find? (fun i => decide (Drift.stableRank P w i = r))).getD 0

/-- Phases in `Drift.classPhases v P w c` ordered by strictly increasing `Drift.stableRank P w`. -/
def rankList (v c : Point) (P : Nat) (w : Nat → Bool) : List Nat :=
  (List.range (Drift.classPhases v P w c).length).map (rankPhase v c P w)

private theorem range_pairwise_lt (n : Nat) : (List.range n).Pairwise (· < ·) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact List.mem_range.mp ha

theorem rankPhase_spec {v c : Point} {P r : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0))
    (hr : r < (Drift.classPhases v P w c).length) :
    rankPhase v c P w r ∈ Drift.classPhases v P w c ∧
      Drift.stableRank P w (rankPhase v c P w r) = r := by
  obtain ⟨i, hiC, hir⟩ := Drift.stableRank_surjective_on_class hd hv hr
  unfold rankPhase
  cases hfind : (Drift.classPhases v P w c).find? (fun j => decide (Drift.stableRank P w j = r)) with
  | none =>
    have hnone := List.find?_eq_none.mp hfind i hiC
    simp [hir] at hnone
  | some x =>
    have hxC : x ∈ Drift.classPhases v P w c := List.mem_of_find?_eq_some hfind
    have hxr : decide (Drift.stableRank P w x = r) = true :=
      List.find?_some (p := fun j => decide (Drift.stableRank P w j = r)) hfind
    exact ⟨hxC, of_decide_eq_true hxr⟩

theorem rankList_length (v c : Point) (P : Nat) (w : Nat → Bool) :
    (rankList v c P w).length = (Drift.classPhases v P w c).length := by
  simp [rankList]

theorem rankList_pairwise_lt {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    (rankList v c P w).Pairwise (fun i j => Drift.stableRank P w i < Drift.stableRank P w j) := by
  unfold rankList
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ (range_pairwise_lt (Drift.classPhases v P w c).length)
  intro r1 r2 hr1 hr2 hlt
  rw [(rankPhase_spec hd hv (List.mem_range.mp hr1)).2,
    (rankPhase_spec hd hv (List.mem_range.mp hr2)).2]
  exact hlt

theorem rankList_nodup {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    (rankList v c P w).Nodup := by
  apply List.Pairwise.imp _ (rankList_pairwise_lt hd hv)
  intro a b hlt he
  rw [he] at hlt
  omega

theorem mem_rankList {v c : Point} {P i : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    i ∈ rankList v c P w ↔ i ∈ Drift.classPhases v P w c := by
  constructor
  · intro hi
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hi
    exact (rankPhase_spec hd hv (List.mem_range.mp hr)).1
  · intro hi
    have hlt := Drift.stableRank_lt_class_length hd hv hi
    have hspec := rankPhase_spec (c := c) hd hv hlt
    have heq : i = rankPhase v c P w (Drift.stableRank P w i) :=
      Drift.stableRank_injective_on_class hd hv hi hspec.1 hspec.2.symm
    rw [heq]
    exact List.mem_map.mpr ⟨Drift.stableRank P w i, List.mem_range.mpr hlt, rfl⟩

theorem rankList_perm_classPhases {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    (rankList v c P w).Perm (Drift.classPhases v P w c) := by
  apply (List.perm_ext_iff_of_nodup (rankList_nodup hd hv) (Drift.classPhases_nodup v P w c)).mpr
  intro i
  exact mem_rankList hd hv

theorem rankList_map_stableRank {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) :
    (rankList v c P w).map (Drift.stableRank P w) =
      List.range (Drift.classPhases v P w c).length := by
  unfold rankList
  rw [List.map_map]
  have hid : ((List.range (Drift.classPhases v P w c).length).map
      (Drift.stableRank P w ∘ rankPhase v c P w)) =
      (List.range (Drift.classPhases v P w c).length).map id := by
    apply List.map_congr_left
    intro r hr
    exact (rankPhase_spec hd hv (List.mem_range.mp hr)).2
  rw [hid, List.map_id]

theorem rankSum_rankList {v c : Point} {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = v) (hv : v ≠ (0, 0)) (p : Nat → Bool) :
    PortInversion.rankSum ((rankList v c P w).map p) =
      (((rankList v c P w).filter p).map (Drift.stableRank P w)).sum := by
  unfold rankList
  rw [List.map_map, rankSum_map_range, List.filter_map, List.map_map]
  have hcongr :
      (((List.range (Drift.classPhases v P w c).length).filter
          (p ∘ rankPhase v c P w)).map (Drift.stableRank P w ∘ rankPhase v c P w)) =
        ((List.range (Drift.classPhases v P w c).length).filter
          (p ∘ rankPhase v c P w)).map id := by
    apply List.map_congr_left
    intro r hr
    have hr' := List.mem_range.mp (List.mem_filter.mp hr).1
    exact (rankPhase_spec hd hv hr').2
  rw [hcongr, List.map_id]

/-! ### `(2, 0)` quotient vertices, ports, counts, and flow/cut balance -/

/-- Rank-ordered phases in the vertical-entry class `Q_y` on row `y`. -/
def QList (P : Nat) (w : Nat → Bool) (y : Int) : List Nat :=
  rankList (2, 0) (qRep y) P w

/-- Rank-ordered phases in the horizontal-entry class `C_y` on row `y`. -/
def CList (P : Nat) (w : Nat → Bool) (y : Int) : List Nat :=
  rankList (2, 0) (cRep y) P w

/-- Global positive outgoing port bit: `true` for `.east` (from `Q_y`) or `.north` (from `C_y`). -/
def outPos (w : Nat → Bool) (i : Nat) : Bool :=
  decide (Drift.outDir w i = .east ∨ Drift.outDir w i = .north)

/-- Global positive incoming port bit: `true` for `.north` (into `Q_y`) or `.east` (into `C_y`). -/
def inPos (w : Nat → Bool) (i : Nat) : Bool :=
  decide (Drift.inDir w i = .north ∨ Drift.inDir w i = .east)

/-- Number of visits to `Q_y` on row `y`. -/
def hCnt (P : Nat) (w : Nat → Bool) (y : Int) : Nat :=
  (QList P w y).length

/-- Directed edge counts leaving row `y`. -/
def wCnt (P : Nat) (w : Nat → Bool) (y : Int) : Nat :=
  (Drift.departures (2, 0) P w (qRep y) .west).length

def eCnt (P : Nat) (w : Nat → Bool) (y : Int) : Nat :=
  (Drift.departures (2, 0) P w (qRep y) .east).length

def sCnt (P : Nat) (w : Nat → Bool) (y : Int) : Nat :=
  (Drift.departures (2, 0) P w (cRep y) .south).length

def nCnt (P : Nat) (w : Nat → Bool) (y : Int) : Nat :=
  (Drift.departures (2, 0) P w (cRep y) .north).length

theorem pos_period_of_drift_two_zero {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) : 0 < P := by
  rcases Nat.eq_zero_or_pos P with rfl | hpos
  · simp [wordDrift, wordPos, wordTrace] at hd
  · exact hpos

theorem even_period_of_north {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) : P % 2 = 0 := by
  have hax := wordTrace_axis w P
  rw [hh] at hax
  simp only [Direction.horizontal] at hax
  by_cases h1 : P % 2 = 1
  · simp [h1] at hax
  · omega

theorem mem_QList {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) :
    i ∈ QList P w y ↔ i < P ∧ (wordPos w i).2 = y ∧ i % 2 = 0 := by
  unfold QList
  rw [mem_rankList hd drift_two_zero_ne_zero, Drift.mem_classPhases, sameClass_qRep_iff]
  have hp := wordPos_sum_parity w i
  omega

theorem mem_CList {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) :
    i ∈ CList P w y ↔ i < P ∧ (wordPos w i).2 = y ∧ i % 2 = 1 := by
  unfold CList
  rw [mem_rankList hd drift_two_zero_ne_zero, Drift.mem_classPhases, sameClass_cRep_iff]
  have hp := wordPos_sum_parity w i
  omega

theorem QList_dirs {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) (hi : i ∈ QList P w y) :
    (Drift.inDir w i = .north ∨ Drift.inDir w i = .south) ∧
    (Drift.outDir w i = .east ∨ Drift.outDir w i = .west) := by
  have hev := ((mem_QList hd).mp hi).2.2
  exact ⟨inDir_vertical_of_even w hev, outDir_horizontal_of_even w hev⟩

theorem CList_dirs {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) (hi : i ∈ CList P w y) :
    (Drift.inDir w i = .east ∨ Drift.inDir w i = .west) ∧
    (Drift.outDir w i = .north ∨ Drift.outDir w i = .south) := by
  have hodd := ((mem_CList hd).mp hi).2.2
  exact ⟨inDir_horizontal_of_odd w hodd, outDir_vertical_of_odd w hodd⟩

theorem inPos_QList {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) (hi : i ∈ QList P w y) :
    inPos w i = decide (Drift.inDir w i = .north) := by
  rcases (QList_dirs hd hi).1 with h | h <;> simp [inPos, h]

theorem outPos_QList {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) (hi : i ∈ QList P w y) :
    outPos w i = decide (Drift.outDir w i = .east) := by
  rcases (QList_dirs hd hi).2 with h | h <;> simp [outPos, h]

theorem inPos_CList {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) (hi : i ∈ CList P w y) :
    inPos w i = decide (Drift.inDir w i = .east) := by
  rcases (CList_dirs hd hi).1 with h | h <;> simp [inPos, h]

theorem outPos_CList {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) (hi : i ∈ CList P w y) :
    outPos w i = decide (Drift.outDir w i = .north) := by
  rcases (CList_dirs hd hi).2 with h | h <;> simp [outPos, h]

theorem QList_left_iff_xor {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) (hi : i ∈ QList P w y) :
    w i = xor (inPos w i) (outPos w i) := by
  rw [inPos_QList hd hi, outPos_QList hd hi]
  rcases (QList_dirs hd hi).1 with hin | hin <;> cases hw : w i <;>
    simp [Drift.outDir, UnitDiagonalMatching.outDir, hin, hw, turn,
      Direction.left, Direction.right]

theorem CList_left_iff_not_xor {P i : Nat} {w : Nat → Bool} {y : Int}
    (hd : wordDrift P w = (2, 0)) (hi : i ∈ CList P w y) :
    w i = !(xor (inPos w i) (outPos w i)) := by
  rw [inPos_CList hd hi, outPos_CList hd hi]
  rcases (CList_dirs hd hi).1 with hin | hin <;> cases hw : w i <;>
    simp [Drift.outDir, UnitDiagonalMatching.outDir, hin, hw, turn,
      Direction.left, Direction.right]

private theorem filter_two_values_length {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → β) {b1 b2 : β} (hne : b1 ≠ b2)
    (hcov : ∀ x ∈ xs, f x = b1 ∨ f x = b2) :
    (xs.filter (fun x => decide (f x = b1))).length +
      (xs.filter (fun x => decide (f x = b2))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hcov x (by simp)
    have hxs := ih (fun y hy => hcov y (by simp [hy]))
    rcases hx with hx1 | hx2
    · simp only [List.filter_cons, hx1, decide_true, ite_true, decide_eq_false hne,
        Bool.false_eq_true, ite_false, List.length_cons]
      omega
    · simp only [List.filter_cons, hx2, decide_true, ite_true, decide_eq_false hne.symm,
        Bool.false_eq_true, ite_false, List.length_cons]
      omega

theorem wCnt_eq_arr_west {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    wCnt P w y = (Drift.arrivals (2, 0) P w (cRep y) .west).length := by
  unfold wCnt
  rw [Drift.departures_length_eq_arrivals_length hh hd,
    Drift.arrivals_congr P w .west (sameClass_move_qRep_west y)]

theorem eCnt_eq_arr_east {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    eCnt P w y = (Drift.arrivals (2, 0) P w (cRep y) .east).length := by
  unfold eCnt
  rw [Drift.departures_length_eq_arrivals_length hh hd,
    Drift.arrivals_congr P w .east (sameClass_move_qRep_east y)]

theorem sCnt_eq_arr_south {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    sCnt P w y = (Drift.arrivals (2, 0) P w (qRep (y - 1)) .south).length := by
  unfold sCnt
  rw [Drift.departures_length_eq_arrivals_length hh hd,
    Drift.arrivals_congr P w .south (sameClass_move_cRep_south y)]

theorem nCnt_eq_arr_north {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    nCnt P w y = (Drift.arrivals (2, 0) P w (qRep (y + 1)) .north).length := by
  unfold nCnt
  rw [Drift.departures_length_eq_arrivals_length hh hd,
    Drift.arrivals_congr P w .north (sameClass_move_cRep_north y)]

theorem wCnt_add_eCnt_eq_hCnt {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) (y : Int) :
    wCnt P w y + eCnt P w y = hCnt P w y := by
  unfold wCnt eCnt hCnt QList Drift.departures
  rw [rankList_length]
  exact filter_two_values_length (Drift.classPhases (2, 0) P w (qRep y)) (Drift.outDir w)
    (b1 := .west) (b2 := .east) (by decide)
    (fun i hi => (QList_dirs hd ((mem_rankList hd drift_two_zero_ne_zero).mpr hi)).2.symm)

theorem CList_length_eq_hCnt {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    (CList P w y).length = hCnt P w y := by
  rw [← wCnt_add_eCnt_eq_hCnt hd y, wCnt_eq_arr_west hh hd y, eCnt_eq_arr_east hh hd y]
  unfold CList Drift.arrivals
  rw [rankList_length]
  exact (filter_two_values_length (Drift.classPhases (2, 0) P w (cRep y)) (Drift.inDir w)
    (b1 := .west) (b2 := .east) (by decide)
    (fun i hi => (CList_dirs hd ((mem_rankList hd drift_two_zero_ne_zero).mpr hi)).1.symm)).symm

theorem sCnt_add_nCnt_eq_hCnt {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    sCnt P w y + nCnt P w y = hCnt P w y := by
  rw [← CList_length_eq_hCnt hh hd y]
  unfold sCnt nCnt CList Drift.departures
  rw [rankList_length]
  exact filter_two_values_length (Drift.classPhases (2, 0) P w (cRep y)) (Drift.outDir w)
    (b1 := .south) (b2 := .north) (by decide)
    (fun i hi => (CList_dirs hd ((mem_rankList hd drift_two_zero_ne_zero).mpr hi)).2.symm)

theorem sCnt_succ_add_nCnt_pred_eq_hCnt {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    sCnt P w (y + 1) + nCnt P w (y - 1) = hCnt P w y := by
  have hs := sCnt_eq_arr_south hh hd (y + 1)
  have hn := nCnt_eq_arr_north hh hd (y - 1)
  rw [show y + 1 - 1 = y by omega] at hs
  rw [show y - 1 + 1 = y by omega] at hn
  rw [hs, hn]
  unfold hCnt QList Drift.arrivals
  rw [rankList_length]
  exact filter_two_values_length (Drift.classPhases (2, 0) P w (qRep y)) (Drift.inDir w)
    (b1 := .south) (b2 := .north) (by decide)
    (fun i hi => (QList_dirs hd ((mem_rankList hd drift_two_zero_ne_zero).mpr hi)).1.symm)

/-! ### Explicit finite row window `[minY, maxY]` and cut balance -/

private def listMin : List Int → Int
  | [] => 0
  | x :: xs => min x (listMin xs)

private def listMax : List Int → Int
  | [] => 0
  | x :: xs => max x (listMax xs)

private theorem listMin_le_mem {x : Int} {xs : List Int} (hx : x ∈ xs) : listMin xs ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [listMin]; omega
    · have := ih hx'; simp only [listMin]; omega

private theorem listMax_ge_mem {x : Int} {xs : List Int} (hx : x ∈ xs) : x ≤ listMax xs := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [listMax]; omega
    · have := ih hx'; simp only [listMax]; omega

private theorem listMin_le_zero (xs : List Int) : listMin xs ≤ 0 := by
  induction xs with
  | nil => simp [listMin]
  | cons a xs ih => simp only [listMin]; omega

private theorem zero_le_listMax (xs : List Int) : 0 ≤ listMax xs := by
  induction xs with
  | nil => simp [listMax]
  | cons a xs ih => simp only [listMax]; omega

/-- Strict lower row bound: every visited phase `i < P` satisfies `minY P w < (wordPos w i).2`. -/
def minY (P : Nat) (w : Nat → Bool) : Int :=
  listMin ((List.range P).map (fun i => (wordPos w i).2)) - 1

/-- Strict upper row bound: every visited phase `i < P` satisfies `(wordPos w i).2 < maxY P w`. -/
def maxY (P : Nat) (w : Nat → Bool) : Int :=
  listMax ((List.range P).map (fun i => (wordPos w i).2)) + 1

/-- Number of row steps between `minY P w` and `maxY P w` (`maxY = minY + rowCount`). -/
def rowCount (P : Nat) (w : Nat → Bool) : Nat :=
  (maxY P w - minY P w).toNat

/-- Increasing list of integer rows `[minY P w, ..., maxY P w]` covering all visited rows with
one empty padding row on each end. -/
def rowList (P : Nat) (w : Nat → Bool) : List Int :=
  (List.range (rowCount P w + 1)).map (fun k : Nat => minY P w + (k : Int))

theorem minY_lt_wordPos {P i : Nat} {w : Nat → Bool} (hi : i < P) :
    minY P w < (wordPos w i).2 := by
  have hmem : (wordPos w i).2 ∈ (List.range P).map (fun j => (wordPos w j).2) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hle := listMin_le_mem hmem
  unfold minY
  omega

theorem wordPos_lt_maxY {P i : Nat} {w : Nat → Bool} (hi : i < P) :
    (wordPos w i).2 < maxY P w := by
  have hmem : (wordPos w i).2 ∈ (List.range P).map (fun j => (wordPos w j).2) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hge := listMax_ge_mem hmem
  unfold maxY
  omega

theorem minY_add_rowCount (P : Nat) (w : Nat → Bool) :
    minY P w + (rowCount P w : Int) = maxY P w := by
  have hlo := listMin_le_zero ((List.range P).map (fun i => (wordPos w i).2))
  have hhi := zero_le_listMax ((List.range P).map (fun i => (wordPos w i).2))
  unfold rowCount minY maxY
  omega

theorem QList_eq_nil_of_outside {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) {y : Int} (hy : y ≤ minY P w ∨ maxY P w ≤ y) :
    QList P w y = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  obtain ⟨hiP, hiy, _⟩ := (mem_QList hd).mp hi
  have hlo := minY_lt_wordPos (w := w) hiP
  have hhi := wordPos_lt_maxY (w := w) hiP
  omega

theorem CList_eq_nil_of_outside {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) {y : Int} (hy : y ≤ minY P w ∨ maxY P w ≤ y) :
    CList P w y = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  obtain ⟨hiP, hiy, _⟩ := (mem_CList hd).mp hi
  have hlo := minY_lt_wordPos (w := w) hiP
  have hhi := wordPos_lt_maxY (w := w) hiP
  omega

theorem counts_zero_of_outside {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0))
    {y : Int} (hy : y ≤ minY P w ∨ maxY P w ≤ y) :
    hCnt P w y = 0 ∧ wCnt P w y = 0 ∧ eCnt P w y = 0 ∧ sCnt P w y = 0 ∧ nCnt P w y = 0 := by
  have hh0 : hCnt P w y = 0 := by unfold hCnt; rw [QList_eq_nil_of_outside hd hy]; rfl
  have hwe := wCnt_add_eCnt_eq_hCnt hd y
  have hsn := sCnt_add_nCnt_eq_hCnt hh hd y
  omega

/-- **Cut balance (L17(1a)):** Across every horizontal cut `y ↔ y + 1`, downward south traffic
equals upward north traffic: `s_{y+1} = n_y`. -/
theorem sCnt_succ_eq_nCnt {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    sCnt P w (y + 1) = nCnt P w y := by
  by_cases hhi : maxY P w ≤ y
  · have h1 := (counts_zero_of_outside hh hd (Or.inr hhi)).2.2.2.2
    have h2 := (counts_zero_of_outside hh hd (Or.inr (show maxY P w ≤ y + 1 by omega))).2.2.2.1
    omega
  · have hdown : ∀ k : Nat, sCnt P w (maxY P w - (k : Int) + 1) = nCnt P w (maxY P w - (k : Int)) := by
      intro k
      induction k with
      | zero =>
        simp only [Int.natCast_zero, Int.sub_zero]
        have h1 := (counts_zero_of_outside hh hd (Or.inr (Int.le_refl _))).2.2.2.2
        have h2 := (counts_zero_of_outside hh hd (Or.inr (by omega : maxY P w ≤ maxY P w + 1))).2.2.2.1
        omega
      | succ k ih =>
        let z : Int := maxY P w - (k : Int)
        have hflow1 := sCnt_add_nCnt_eq_hCnt hh hd z
        have hflow2 := sCnt_succ_add_nCnt_pred_eq_hCnt hh hd z
        have hz1 : maxY P w - ((k + 1 : Nat) : Int) + 1 = z := by dsimp [z]; omega
        have hz2 : maxY P w - ((k + 1 : Nat) : Int) = z - 1 := by dsimp [z]; omega
        rw [hz1, hz2]
        dsimp [z] at ih hflow1 hflow2 ⊢
        omega
    let k : Nat := (maxY P w - y).toNat
    have hk : maxY P w - (k : Int) = y := by dsimp [k]; omega
    have h := hdown k
    rwa [hk] at h

/-- **Row multiplicity identity (L17(1b)):** `h_y = n_{y-1} + n_y` for every row `y`. -/
theorem hCnt_eq_nCnt_pred_add_nCnt {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    hCnt P w y = nCnt P w (y - 1) + nCnt P w y := by
  have h1 := sCnt_add_nCnt_eq_hCnt hh hd y
  have h2 := sCnt_succ_eq_nCnt hh hd (y - 1)
  rw [show y - 1 + 1 = y by omega] at h2
  omega

/-- Row-ordered vertex block list `[Q_{y0}, C_{y0}, Q_{y0+1}, C_{y0+1}, ...]`. -/
def vertexBlocks (P : Nat) (w : Nat → Bool) : List (List Nat) :=
  ((rowList P w).map (fun y => [QList P w y, CList P w y])).flatten

private theorem nodup_flatten_of_disjoint' {α : Type} (L : List (List α))
    (hnd : ∀ xs ∈ L, xs.Nodup)
    (hdisj : L.Pairwise (fun xs ys => ∀ a, a ∈ xs → a ∉ ys)) :
    L.flatten.Nodup := by
  induction L with
  | nil => simp
  | cons xs L ih =>
    rw [List.flatten_cons, List.nodup_append]
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdisj
    refine ⟨hnd xs (by simp), ih (fun ys hys => hnd ys (by simp [hys])) htail, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨ys, hys, hay⟩ := List.mem_flatten.mp hb
    exact hhead ys hys a ha hay

theorem mem_rowList_iff {P : Nat} {w : Nat → Bool} {y : Int} :
    y ∈ rowList P w ↔ minY P w ≤ y ∧ y ≤ maxY P w := by
  have hmax := minY_add_rowCount P w
  unfold rowList
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' := List.mem_range.mp hk
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(y - minY P w).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

theorem rowList_nodup (P : Nat) (w : Nat → Bool) : (rowList P w).Nodup := by
  unfold rowList
  apply List.Pairwise.imp _ (List.pairwise_map.mpr
    (List.Pairwise.imp (fun h => by omega : ∀ a b : Nat, a < b → minY P w + (a : Int) ≠ minY P w + (b : Int))
      (range_pairwise_lt (rowCount P w + 1))))
  intro _ _ h
  exact h

theorem vertexBlocks_nodup_each {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) :
    ∀ b ∈ vertexBlocks P w, b.Nodup := by
  intro b hb
  obtain ⟨pair, hpair, hbpair⟩ := List.mem_flatten.mp hb
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbpair
  rcases hbpair with rfl | rfl
  · exact rankList_nodup hd drift_two_zero_ne_zero
  · exact rankList_nodup hd drift_two_zero_ne_zero

theorem vertexBlocks_flatten_perm_range {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) :
    (vertexBlocks P w).flatten.Perm (List.range P) := by
  have hrow_perm :
      (vertexBlocks P w).flatten =
        ((rowList P w).map (fun y => QList P w y ++ CList P w y)).flatten := by
    unfold vertexBlocks
    induction rowList P w with
    | nil => simp
    | cons y ys ih => simp [ih]
  rw [hrow_perm]
  have hnd : (((rowList P w).map (fun y => QList P w y ++ CList P w y)).flatten).Nodup := by
    apply nodup_flatten_of_disjoint'
    · intro xs hxs
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hxs
      rw [List.nodup_append]
      refine ⟨rankList_nodup hd drift_two_zero_ne_zero, rankList_nodup hd drift_two_zero_ne_zero, ?_⟩
      intro a ha b hb hab
      subst hab
      have h0 := ((mem_QList hd).mp ha).2.2
      have h1 := ((mem_CList hd).mp hb).2.2
      omega
    · rw [List.pairwise_map]
      apply List.Pairwise.imp _ (rowList_nodup P w)
      intro y1 y2 hne i hi1 hi2
      have hy1 : (wordPos w i).2 = y1 := by
        rcases List.mem_append.mp hi1 with hq | hc
        · exact ((mem_QList hd).mp hq).2.1
        · exact ((mem_CList hd).mp hc).2.1
      have hy2 : (wordPos w i).2 = y2 := by
        rcases List.mem_append.mp hi2 with hq | hc
        · exact ((mem_QList hd).mp hq).2.1
        · exact ((mem_CList hd).mp hc).2.1
      exact hne (hy1.symm.trans hy2)
  apply (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr
  intro i
  rw [List.mem_flatten, List.mem_range]
  constructor
  · rintro ⟨xs, hxs, hix⟩
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hxs
    rcases List.mem_append.mp hix with hq | hc
    · exact ((mem_QList hd).mp hq).1
    · exact ((mem_CList hd).mp hc).1
  · intro hiP
    have hlo := minY_lt_wordPos (w := w) hiP
    have hhi := wordPos_lt_maxY (w := w) hiP
    refine ⟨QList P w (wordPos w i).2 ++ CList P w (wordPos w i).2,
      List.mem_map.mpr ⟨(wordPos w i).2, mem_rowList_iff.mpr ⟨by omega, by omega⟩, rfl⟩, ?_⟩
    by_cases hev : i % 2 = 0
    · exact List.mem_append_left _ ((mem_QList hd).mpr ⟨hiP, rfl, hev⟩)
    · exact List.mem_append_right _ ((mem_CList hd).mpr ⟨hiP, rfl, by omega⟩)

private theorem nat_sum_shift_eq_of_zero {f : Int → Nat} {y0 : Int} {m : Nat}
    (hlo : f (y0 - 1) = 0) (hhi : f (y0 + (m : Int)) = 0) :
    ((List.range (m + 1)).map (fun k : Nat => f (y0 + (k : Int) - 1))).sum =
      ((List.range (m + 1)).map (fun k : Nat => f (y0 + (k : Int)))).sum := by
  have hgen : ∀ n : Nat,
      ((List.range n).map (fun k : Nat => f (y0 + (k : Int) - 1))).sum + f (y0 + (n : Int) - 1) =
        f (y0 - 1) + ((List.range n).map (fun k : Nat => f (y0 + (k : Int)))).sum := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append, nat_sum_append, nat_sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      have he : y0 + ((n + 1 : Nat) : Int) - 1 = y0 + (n : Int) := by omega
      rw [he]
      omega
  have h := hgen (m + 1)
  have he : y0 + ((m + 1 : Nat) : Int) - 1 = y0 + (m : Int) := by omega
  rw [he, hlo, hhi] at h
  omega

/-- **Period/cut sum identity (L17(1c)):** `P = 4 * ∑_y n_y`, so `4 ∣ P` and `∑_y n_y = P / 4`. -/
theorem four_mul_sum_nCnt_eq_period {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) :
    4 * ((rowList P w).map (nCnt P w)).sum = P := by
  have hperm := vertexBlocks_flatten_perm_range hd
  have hlen := hperm.length_eq
  rw [List.length_range] at hlen
  have hflat : (vertexBlocks P w).flatten.length =
      ((rowList P w).map (fun y => 2 * hCnt P w y)).sum := by
    have haux : ∀ ys : List Int,
        ((ys.map (fun y => [QList P w y, CList P w y])).flatten).flatten.length =
          (ys.map (fun y => 2 * hCnt P w y)).sum := by
      intro ys
      induction ys with
      | nil => simp
      | cons y ys ih =>
        simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
          List.length_append, List.sum_cons, ih, CList_length_eq_hCnt hh hd y]
        unfold hCnt
        omega
    exact haux (rowList P w)
  have hsum_h : ((rowList P w).map (fun y => 2 * hCnt P w y)).sum =
      2 * ((rowList P w).map (fun y => nCnt P w (y - 1))).sum +
        2 * ((rowList P w).map (nCnt P w)).sum := by
    have h2 : ∀ xs : List Int, ∀ f : Int → Nat, (xs.map (fun y => 2 * f y)).sum = 2 * (xs.map f).sum := by
      intro xs f
      induction xs with
      | nil => simp
      | cons y ys ih => simp only [List.map_cons, List.sum_cons, ih]; omega
    rw [h2, nat_sum_map_congr (fun y _ => hCnt_eq_nCnt_pred_add_nCnt hh hd y), nat_sum_map_add]
    omega
  have hshift : ((rowList P w).map (fun y => nCnt P w (y - 1))).sum =
      ((rowList P w).map (nCnt P w)).sum := by
    unfold rowList
    rw [List.map_map, List.map_map]
    exact nat_sum_shift_eq_of_zero (f := nCnt P w) (y0 := minY P w) (m := rowCount P w)
      (counts_zero_of_outside hh hd (Or.inl (by omega))).2.2.2.2
      (by rw [minY_add_rowCount]; exact (counts_zero_of_outside hh hd (Or.inr (Int.le_refl _))).2.2.2.2)
  omega

theorem period_mod_four_of_drift_two_zero {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) :
    P % 4 = 0 := by
  have h := four_mul_sum_nCnt_eq_period hh hd
  omega

theorem sum_nCnt_eq_period_div_four {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) :
    ((rowList P w).map (nCnt P w)).sum = P / 4 := by
  have h := four_mul_sum_nCnt_eq_period hh hd
  omega

/-! ### Local left-turn stable-rank sum (L17(2)–(3)) -/

/-- Total left-turn stable-rank sum `K = ∑_{i < P, w i = true} stableRank P w i`. -/
def leftRankSum (P : Nat) (w : Nat → Bool) : Nat :=
  (((List.range P).filter w).map (Drift.stableRank P w)).sum

private theorem filter_xor_sum_mod_two (xs : List Nat) (f g : Nat → Bool) (r : Nat → Nat) :
    (((xs.filter (fun x => xor (f x) (g x))).map r).sum) % 2 =
      (((xs.filter f).map r).sum + ((xs.filter g).map r).sum) % 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hfx : f x <;> cases hgx : g x <;> simp [hfx, hgx] <;> omega

private theorem filter_not_xor_sum_mod_two (xs : List Nat) (f g : Nat → Bool) (r : Nat → Nat) :
    (((xs.filter (fun x => !(xor (f x) (g x)))).map r).sum) % 2 =
      ((xs.map r).sum + ((xs.filter f).map r).sum + ((xs.filter g).map r).sum) % 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hfx : f x <;> cases hgx : g x <;> simp [hfx, hgx] <;> omega

theorem countTrue_inPos_QList {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    PortInversion.countTrue ((QList P w y).map (inPos w)) = nCnt P w (y - 1) := by
  rw [PortInversion.countTrue_map]
  have hfeq : (QList P w y).filter (inPos w) =
      (QList P w y).filter (fun i => decide (Drift.inDir w i = .north)) :=
    List.filter_congr (fun i hi => inPos_QList hd hi)
  rw [hfeq]
  have hperm := (rankList_perm_classPhases (c := qRep y) hd drift_two_zero_ne_zero).filter
    (fun i => decide (Drift.inDir w i = .north))
  have hn := nCnt_eq_arr_north hh hd (y - 1)
  rw [show y - 1 + 1 = y by omega] at hn
  unfold QList
  rw [hperm.length_eq, hn]
  rfl

theorem countTrue_outPos_QList {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) (y : Int) :
    PortInversion.countTrue ((QList P w y).map (outPos w)) = eCnt P w y := by
  rw [PortInversion.countTrue_map]
  have hfeq : (QList P w y).filter (outPos w) =
      (QList P w y).filter (fun i => decide (Drift.outDir w i = .east)) :=
    List.filter_congr (fun i hi => outPos_QList hd hi)
  rw [hfeq]
  have hperm := (rankList_perm_classPhases (c := qRep y) hd drift_two_zero_ne_zero).filter
    (fun i => decide (Drift.outDir w i = .east))
  unfold QList
  rw [hperm.length_eq]
  rfl

theorem countTrue_inPos_CList {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    PortInversion.countTrue ((CList P w y).map (inPos w)) = eCnt P w y := by
  rw [PortInversion.countTrue_map]
  have hfeq : (CList P w y).filter (inPos w) =
      (CList P w y).filter (fun i => decide (Drift.inDir w i = .east)) :=
    List.filter_congr (fun i hi => inPos_CList hd hi)
  rw [hfeq]
  have hperm := (rankList_perm_classPhases (c := cRep y) hd drift_two_zero_ne_zero).filter
    (fun i => decide (Drift.inDir w i = .east))
  unfold CList
  rw [hperm.length_eq, eCnt_eq_arr_east hh hd y]
  rfl

theorem countTrue_outPos_CList {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) (y : Int) :
    PortInversion.countTrue ((CList P w y).map (outPos w)) = nCnt P w y := by
  rw [PortInversion.countTrue_map]
  have hfeq : (CList P w y).filter (outPos w) =
      (CList P w y).filter (fun i => decide (Drift.outDir w i = .north)) :=
    List.filter_congr (fun i hi => outPos_CList hd hi)
  rw [hfeq]
  have hperm := (rankList_perm_classPhases (c := cRep y) hd drift_two_zero_ne_zero).filter
    (fun i => decide (Drift.outDir w i = .north))
  unfold CList
  rw [hperm.length_eq]
  rfl

/-- Row-wise local L17 identity: on every single row `y`, the left-turn stable-rank sum on
`Q_y ∪ C_y` equals the four port-word inversion counts plus `n_{y-1} * n_y` modulo 2. -/
theorem row_leftRankSum_mod_two {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    ((((QList P w y).filter w).map (Drift.stableRank P w)).sum +
      (((CList P w y).filter w).map (Drift.stableRank P w)).sum) % 2 =
    (PortInversion.wordInv ((QList P w y).map (inPos w)) +
      PortInversion.wordInv ((QList P w y).map (outPos w)) +
      PortInversion.wordInv ((CList P w y).map (inPos w)) +
      PortInversion.wordInv ((CList P w y).map (outPos w)) +
      nCnt P w (y - 1) * nCnt P w y) % 2 := by
  have hQf : (QList P w y).filter w =
      (QList P w y).filter (fun i => xor (inPos w i) (outPos w i)) :=
    List.filter_congr (fun i hi => QList_left_iff_xor hd hi)
  have hCf : (CList P w y).filter w =
      (CList P w y).filter (fun i => !(xor (inPos w i) (outPos w i))) :=
    List.filter_congr (fun i hi => CList_left_iff_not_xor hd hi)
  have hQxor := filter_xor_sum_mod_two (QList P w y) (inPos w) (outPos w) (Drift.stableRank P w)
  have hCxor := filter_not_xor_sum_mod_two (CList P w y) (inPos w) (outPos w) (Drift.stableRank P w)
  rw [← hQf] at hQxor
  rw [← hCf] at hCxor
  have hCsum : ((CList P w y).map (Drift.stableRank P w)).sum = PortInversion.pairCount (hCnt P w y) := by
    unfold CList
    rw [rankList_map_stableRank hd drift_two_zero_ne_zero, sum_range_eq_pairCount]
    have hlen := CList_length_eq_hCnt hh hd y
    unfold CList at hlen
    rw [rankList_length] at hlen
    rw [hlen]
  rw [hCsum] at hCxor
  have hrQ1 : PortInversion.rankSum ((QList P w y).map (inPos w)) =
      (((QList P w y).filter (inPos w)).map (Drift.stableRank P w)).sum :=
    rankSum_rankList hd drift_two_zero_ne_zero (inPos w)
  have hrQ2 : PortInversion.rankSum ((QList P w y).map (outPos w)) =
      (((QList P w y).filter (outPos w)).map (Drift.stableRank P w)).sum :=
    rankSum_rankList hd drift_two_zero_ne_zero (outPos w)
  have hrC1 : PortInversion.rankSum ((CList P w y).map (inPos w)) =
      (((CList P w y).filter (inPos w)).map (Drift.stableRank P w)).sum :=
    rankSum_rankList hd drift_two_zero_ne_zero (inPos w)
  have hrC2 : PortInversion.rankSum ((CList P w y).map (outPos w)) =
      (((CList P w y).filter (outPos w)).map (Drift.stableRank P w)).sum :=
    rankSum_rankList hd drift_two_zero_ne_zero (outPos w)
  rw [← hrQ1, ← hrQ2] at hQxor
  rw [← hrC1, ← hrC2] at hCxor
  have hp1 := PortInversion.portWord_parity ((QList P w y).map (inPos w))
  have hp2 := PortInversion.portWord_parity ((QList P w y).map (outPos w))
  have hp3 := PortInversion.portWord_parity ((CList P w y).map (inPos w))
  have hp4 := PortInversion.portWord_parity ((CList P w y).map (outPos w))
  rw [List.length_map, countTrue_inPos_QList hh hd y] at hp1
  rw [List.length_map, countTrue_outPos_QList hd y] at hp2
  rw [List.length_map, countTrue_inPos_CList hh hd y, CList_length_eq_hCnt hh hd y] at hp3
  rw [List.length_map, countTrue_outPos_CList hd y, CList_length_eq_hCnt hh hd y] at hp4
  change (PortInversion.wordInv ((QList P w y).map (inPos w)) +
      nCnt P w (y - 1) * (hCnt P w y - 1) +
      PortInversion.rankSum ((QList P w y).map (inPos w)) +
      PortInversion.pairCount (nCnt P w (y - 1))) % 2 = 0 at hp1
  change (PortInversion.wordInv ((QList P w y).map (outPos w)) +
      eCnt P w y * (hCnt P w y - 1) +
      PortInversion.rankSum ((QList P w y).map (outPos w)) +
      PortInversion.pairCount (eCnt P w y)) % 2 = 0 at hp2
  have hh_eq := hCnt_eq_nCnt_pred_add_nCnt hh hd y
  have hpc := pairCount_add (nCnt P w (y - 1)) (nCnt P w y)
  rw [← hh_eq] at hpc
  have hlin : (nCnt P w (y - 1) * (hCnt P w y - 1) + nCnt P w y * (hCnt P w y - 1)) % 2 = 0 := by
    rw [← Nat.add_mul, ← hh_eq, ← PortInversion.two_mul_pairCount]
    omega
  omega

/-- Total port-word inversion sum `∑_{v ∈ V} (wordInv α_v + wordInv β_v)`. -/
def totalWordInv (P : Nat) (w : Nat → Bool) : Nat :=
  ((vertexBlocks P w).map (fun b =>
    PortInversion.wordInv (b.map (inPos w)) + PortInversion.wordInv (b.map (outPos w)))).sum

theorem totalWordInv_eq_row_sum (P : Nat) (w : Nat → Bool) :
    totalWordInv P w =
      ((rowList P w).map (fun y =>
        PortInversion.wordInv ((QList P w y).map (inPos w)) +
        PortInversion.wordInv ((QList P w y).map (outPos w)) +
        PortInversion.wordInv ((CList P w y).map (inPos w)) +
        PortInversion.wordInv ((CList P w y).map (outPos w)))).sum := by
  unfold totalWordInv vertexBlocks
  have haux : ∀ ys : List Int,
      ((((ys.map (fun y => [QList P w y, CList P w y])).flatten).map (fun b =>
        PortInversion.wordInv (b.map (inPos w)) + PortInversion.wordInv (b.map (outPos w)))).sum) =
      (ys.map (fun y =>
        PortInversion.wordInv ((QList P w y).map (inPos w)) +
        PortInversion.wordInv ((QList P w y).map (outPos w)) +
        PortInversion.wordInv ((CList P w y).map (inPos w)) +
        PortInversion.wordInv ((CList P w y).map (outPos w)))).sum := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
        List.sum_cons, ih]
      omega
  exact haux (rowList P w)

/-- **L17 (global left-turn stable-rank sum, product form):**
`K ≡ totalWordInv + ∑_y n_{y-1} * n_y (mod 2)`. -/
theorem leftRankSum_mod_two_eq_wordInv_add_prod {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) :
    leftRankSum P w % 2 =
      (totalWordInv P w +
        ((rowList P w).map (fun y => nCnt P w (y - 1) * nCnt P w y)).sum) % 2 := by
  have hperm := (vertexBlocks_flatten_perm_range hd).filter w
  have hK : leftRankSum P w =
      ((rowList P w).map (fun y =>
        (((QList P w y).filter w).map (Drift.stableRank P w)).sum +
        (((CList P w y).filter w).map (Drift.stableRank P w)).sum)).sum := by
    unfold leftRankSum
    rw [← PortInversion.perm_sum (hperm.map (Drift.stableRank P w))]
    unfold vertexBlocks
    have haux : ∀ ys : List Int,
        (((((ys.map (fun y => [QList P w y, CList P w y])).flatten).flatten.filter w).map
          (Drift.stableRank P w)).sum) =
        (ys.map (fun y =>
          (((QList P w y).filter w).map (Drift.stableRank P w)).sum +
          (((CList P w y).filter w).map (Drift.stableRank P w)).sum)).sum := by
      intro ys
      induction ys with
      | nil => simp
      | cons y ys ih =>
        simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
          List.filter_append, List.map_append, nat_sum_append, List.sum_cons, ih]
        omega
    exact haux (rowList P w)
  rw [hK, totalWordInv_eq_row_sum, ← nat_sum_map_add]
  exact nat_sum_map_mod_congr (fun y _ => row_leftRankSum_mod_two hh hd y)

/-- **L17 (blueprint form):**
`K ≡ totalWordInv + ∑_y pairCount h_y (mod 2)`. -/
theorem leftRankSum_mod_two_eq_wordInv_add_pairCount {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) :
    leftRankSum P w % 2 =
      (totalWordInv P w +
        ((rowList P w).map (fun y => PortInversion.pairCount (hCnt P w y))).sum) % 2 := by
  rw [leftRankSum_mod_two_eq_wordInv_add_prod hh hd]
  have hpair : ((rowList P w).map (fun y => PortInversion.pairCount (hCnt P w y))).sum =
      ((rowList P w).map (fun y => PortInversion.pairCount (nCnt P w (y - 1)))).sum +
      ((rowList P w).map (fun y => PortInversion.pairCount (nCnt P w y))).sum +
      ((rowList P w).map (fun y => nCnt P w (y - 1) * nCnt P w y)).sum := by
    rw [← nat_sum_map_add, ← nat_sum_map_add]
    apply nat_sum_map_congr
    intro y _
    rw [hCnt_eq_nCnt_pred_add_nCnt hh hd y, pairCount_add]
  have hshift : ((rowList P w).map (fun y => PortInversion.pairCount (nCnt P w (y - 1)))).sum =
      ((rowList P w).map (fun y => PortInversion.pairCount (nCnt P w y))).sum := by
    unfold rowList
    rw [List.map_map, List.map_map]
    exact nat_sum_shift_eq_of_zero
      (f := fun y => PortInversion.pairCount (nCnt P w y)) (y0 := minY P w) (m := rowCount P w)
      (by rw [(counts_zero_of_outside hh hd (Or.inl (by omega))).2.2.2.2]; rfl)
      (by rw [minY_add_rowCount, (counts_zero_of_outside hh hd (Or.inr (Int.le_refl _))).2.2.2.2]; rfl)
  rw [hpair, hshift]
  omega

/-! ## 4. L18: Edge-block crossing inversion `E` and kinematic rank identity `K ≡ 1 + P / 4 (mod 2)` -/

/-! ### Abstract 3-block sliding-window permutation (`[H_y, S_y, N_y]` ↔ `[S_{y+1}, N_{y-1}, H_y]`) -/

private theorem perm_pull_front {α : Type} :
    ∀ (pre suf : List α) (x : α), (pre ++ x :: suf).Perm (x :: (pre ++ suf))
  | [], _, _ => List.Perm.refl _
  | a :: pre, suf, x =>
    (List.Perm.cons a (perm_pull_front pre suf x)).trans (List.Perm.swap x a (pre ++ suf))

/-- Departure-order 3-block list `[H_y, S_y, N_y, H_{y+1}, S_{y+1}, N_{y+1}, ...]` for `k` rows. -/
def depRest (H S N : Int → List Nat) (y : Int) : Nat → List (List Nat)
  | 0 => []
  | k + 1 => H y :: S y :: N y :: depRest H S N (y + 1) k

/-- Sliding-window departure state at row `y` with pending `N (y - 1)` in front and `k` further rows. -/
def depState (H S N : Int → List Nat) (y : Int) (k : Nat) : List (List Nat) :=
  N (y - 1) :: H y :: N y :: depRest H S N (y + 1) k

/-- Arrival-order 3-block list `[S_{y+1}, N_{y-1}, H_y, ...]` for `k + 1` rows. -/
def arrState (H S N : Int → List Nat) (y : Int) : Nat → List (List Nat)
  | 0 => [S (y + 1), N (y - 1), H y]
  | k + 1 => S (y + 1) :: N (y - 1) :: H y :: arrState H S N (y + 1) k

theorem depState_perm_arrState (H S N : Int → List Nat) :
    ∀ (k : Nat) (y : Int),
      N (y + (k : Int)) = [] → S (y + (k : Int) + 1) = [] →
      (depState H S N y k).Perm (arrState H S N y k)
  | 0, y, hNend, hSend => by
    simp only [Int.natCast_zero, Int.add_zero] at hNend hSend
    simp only [depState, depRest, arrState, hNend, hSend]
    exact perm_pull_front [N (y - 1), H y] [] []
  | k + 1, y, hNend, hSend => by
    have hpull :
        (depState H S N y (k + 1)).Perm
          (S (y + 1) :: N (y - 1) :: H y ::
            (N y :: H (y + 1) :: N (y + 1) :: depRest H S N (y + 1 + 1) k)) :=
      perm_pull_front [N (y - 1), H y, N y, H (y + 1)]
        (N (y + 1) :: depRest H S N (y + 1 + 1) k) (S (y + 1))
    have htail :
        (N y :: H (y + 1) :: N (y + 1) :: depRest H S N (y + 1 + 1) k) =
          depState H S N (y + 1) k := by
      unfold depState
      rw [show y + 1 - 1 = y by omega]
    rw [htail] at hpull
    have hN' : N (y + 1 + (k : Int)) = [] := by
      rwa [show y + 1 + (k : Int) = y + ((k + 1 : Nat) : Int) by omega]
    have hS' : S (y + 1 + (k : Int) + 1) = [] := by
      rwa [show y + 1 + (k : Int) + 1 = y + ((k + 1 : Nat) : Int) + 1 by omega]
    have ih := depState_perm_arrState H S N k (y + 1) hN' hS'
    exact hpull.trans (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ ih)))

theorem depRest_perm_depState (H S N : Int → List Nat) (y0 : Int) (k : Nat)
    (hS0 : S y0 = []) (hN0 : N (y0 - 1) = []) :
    (depRest H S N y0 (k + 1)).Perm (depState H S N y0 k) := by
  simp only [depRest, depState, hS0, hN0]
  exact List.Perm.swap [] (H y0) (N y0 :: depRest H S N (y0 + 1) k)

theorem pairCross_depRest_eq_depState (H S N : Int → List Nat) (y0 : Int) (k : Nat)
    (hS0 : S y0 = []) (hN0 : N (y0 - 1) = []) :
    PortInversion.pairCross (depRest H S N y0 (k + 1)) =
      PortInversion.pairCross (depState H S N y0 k) := by
  simp [depRest, depState, hS0, hN0, PortInversion.pairCross]

theorem pairCross_depState_arrState_mod (H S N : Int → List Nat) :
    ∀ (k : Nat) (y : Int),
      (depState H S N y k).flatten.Nodup →
      N (y + (k : Int)) = [] → S (y + (k : Int) + 1) = [] →
      (PortInversion.pairCross (depState H S N y k) +
        PortInversion.pairCross (arrState H S N y k)) % 2 =
      ((List.range k).map (fun j : Nat =>
        ((N (y + (j : Int) - 1)).length + (H (y + (j : Int))).length +
          (N (y + (j : Int))).length + (H (y + (j : Int) + 1)).length) *
        (S (y + (j : Int) + 1)).length)).sum % 2
  | 0, y, _, hNend, hSend => by
    simp only [Int.natCast_zero, Int.add_zero] at hNend hSend
    have hd : depState H S N y 0 = [N (y - 1), H y] ++ [[]] := by
      simp [depState, depRest, hNend]
    have ha : arrState H S N y 0 = [] :: [N (y - 1), H y] := by
      simp [arrState, hSend]
    rw [hd, ha, pairCross_append_nil, pairCross_cons_nil]
    simp
    omega
  | k + 1, y, hnd, hNend, hSend => by
    let pre : List (List Nat) := [N (y - 1), H y, N y, H (y + 1)]
    let suf : List (List Nat) := N (y + 1) :: depRest H S N (y + 1 + 1) k
    have hdep_eq : depState H S N y (k + 1) = pre ++ S (y + 1) :: suf := rfl
    have hdisj : ∀ a ∈ pre.flatten, ∀ b ∈ S (y + 1), a ≠ b := by
      intro a ha b hb
      rw [hdep_eq, List.flatten_append, List.flatten_cons, List.nodup_append] at hnd
      exact hnd.2.2 a ha b (List.mem_append_left _ hb)
    have hpull_pc := pairCross_pull_to_front_mod pre suf (S (y + 1)) hdisj
    rw [← hdep_eq] at hpull_pc
    have hpre_len : pre.flatten.length =
        (N (y - 1)).length + (H y).length + (N y).length + (H (y + 1)).length := by
      simp only [pre, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
      omega
    rw [hpre_len] at hpull_pc
    have hpulled_eq : S (y + 1) :: (pre ++ suf) =
        [S (y + 1), N (y - 1), H y] ++ depState H S N (y + 1) k := by
      simp only [pre, suf, depState, List.cons_append, List.nil_append]
      rw [show y + 1 - 1 = y by omega]
    have harr_eq : arrState H S N y (k + 1) =
        [S (y + 1), N (y - 1), H y] ++ arrState H S N (y + 1) k := rfl
    have hN' : N (y + 1 + (k : Int)) = [] := by
      rwa [show y + 1 + (k : Int) = y + ((k + 1 : Nat) : Int) by omega]
    have hS' : S (y + 1 + (k : Int) + 1) = [] := by
      rwa [show y + 1 + (k : Int) + 1 = y + ((k + 1 : Nat) : Int) + 1 by omega]
    have hperm_tail := depState_perm_arrState H S N k (y + 1) hN' hS'
    have hstrip := pairCross_strip_prefix_mod [S (y + 1), N (y - 1), H y]
      (depState H S N (y + 1) k) (arrState H S N (y + 1) k) hperm_tail.flatten
    rw [← hpulled_eq, ← harr_eq] at hstrip
    have hnd_tail : (depState H S N (y + 1) k).flatten.Nodup := by
      have hp : (depState H S N y (k + 1)).flatten.Perm
          (([S (y + 1), N (y - 1), H y] ++ depState H S N (y + 1) k).flatten) := by
        rw [← hpulled_eq, hdep_eq]
        exact (perm_pull_front pre suf (S (y + 1))).flatten
      have hnd' := hp.nodup hnd
      rw [List.flatten_append, List.nodup_append] at hnd'
      exact hnd'.2.1
    have ih := pairCross_depState_arrState_mod H S N k (y + 1) hnd_tail hN' hS'
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have h0 :
        ((N (y + ((0 : Nat) : Int) - 1)).length + (H (y + ((0 : Nat) : Int))).length +
          (N (y + ((0 : Nat) : Int))).length + (H (y + ((0 : Nat) : Int) + 1)).length) *
        (S (y + ((0 : Nat) : Int) + 1)).length =
        ((N (y - 1)).length + (H y).length + (N y).length + (H (y + 1)).length) *
          (S (y + 1)).length := by
      simp
    have hrest :
        ((List.range k).map ((fun j : Nat =>
          ((N (y + (j : Int) - 1)).length + (H (y + (j : Int))).length +
            (N (y + (j : Int))).length + (H (y + (j : Int) + 1)).length) *
          (S (y + (j : Int) + 1)).length) ∘ (· + 1))).sum =
        ((List.range k).map (fun j : Nat =>
          ((N (y + 1 + (j : Int) - 1)).length + (H (y + 1 + (j : Int))).length +
            (N (y + 1 + (j : Int))).length + (H (y + 1 + (j : Int) + 1)).length) *
          (S (y + 1 + (j : Int) + 1)).length)).sum := by
      apply nat_sum_map_congr
      intro j _
      simp only [Function.comp_def]
      rw [show y + ((j + 1 : Nat) : Int) = y + 1 + (j : Int) by omega]
    rw [h0, hrest]
    omega

/-! ### Ordered-matching instantiation on the `(2, 0)` successor cycle -/

private theorem nodup_map_on' {α β : Type} {xs : List α} {f : α → β}
    (hn : xs.Nodup) (hf : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
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

/-- Universal ordered-matching list equality: mapping `Drift.succ P` over the `d`-departures
in a rank-sorted source class equals the `d`-arrivals in the rank-sorted target class. -/
theorem rankList_filter_outDir_map_succ {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0))
    {c1 c2 : Point} {d : Direction} (ht : Drift.SameClass (2, 0) (move c1 d) c2) :
    ((rankList (2, 0) c1 P w).filter (fun i => decide (Drift.outDir w i = d))).map (Drift.succ P) =
      (rankList (2, 0) c2 P w).filter (fun i => decide (Drift.inDir w i = d)) := by
  apply eq_of_perm_pairwise_lt (Drift.stableRank P w)
  · have hp1 : ((rankList (2, 0) c1 P w).filter (fun i => decide (Drift.outDir w i = d))).Perm
        (Drift.departures (2, 0) P w c1 d) :=
      (rankList_perm_classPhases hd drift_two_zero_ne_zero).filter _
    have hp2 : ((Drift.departures (2, 0) P w c1 d).map (Drift.succ P)).Perm
        (Drift.arrivals (2, 0) P w (move c1 d) d) := by
      apply (List.perm_ext_iff_of_nodup
        (nodup_map_on' (Drift.departures_nodup (2, 0) P w c1 d)
          (fun _ hj _ hk =>
            UnitDiagonalMatching.succ_injective
              (Drift.mem_departures.mp hj).1 (Drift.mem_departures.mp hk).1))
        (Drift.arrivals_nodup (2, 0) P w (move c1 d) d)).mpr
      intro j
      simpa only [List.mem_map] using (Drift.successor_onto hh hd j).symm
    have hp3 : (Drift.arrivals (2, 0) P w c2 d).Perm
        ((rankList (2, 0) c2 P w).filter (fun i => decide (Drift.inDir w i = d))) :=
      (rankList_perm_classPhases hd drift_two_zero_ne_zero).symm.filter _
    rw [Drift.arrivals_congr P w d ht] at hp2
    exact (hp1.map (Drift.succ P)).trans (hp2.trans hp3)
  · rw [List.pairwise_map]
    have hpw := (rankList_pairwise_lt (c := c1) hd drift_two_zero_ne_zero).filter
      (fun i => decide (Drift.outDir w i = d))
    apply List.Pairwise.imp_of_mem _ hpw
    intro i j hi hj hlt
    have hiD : i ∈ Drift.departures (2, 0) P w c1 d := by
      obtain ⟨hiR, hid⟩ := List.mem_filter.mp hi
      obtain ⟨hiP, hisc⟩ := Drift.mem_classPhases.mp ((mem_rankList hd drift_two_zero_ne_zero).mp hiR)
      exact Drift.mem_departures.mpr ⟨hiP, hisc, of_decide_eq_true hid⟩
    have hjD : j ∈ Drift.departures (2, 0) P w c1 d := by
      obtain ⟨hjR, hjd⟩ := List.mem_filter.mp hj
      obtain ⟨hjP, hjsc⟩ := Drift.mem_classPhases.mp ((mem_rankList hd drift_two_zero_ne_zero).mp hjR)
      exact Drift.mem_departures.mpr ⟨hjP, hjsc, of_decide_eq_true hjd⟩
    exact (Drift.successor_rank_order hd drift_two_zero_ne_zero hiD hjD).mp hlt
  · exact (rankList_pairwise_lt (c := c2) hd drift_two_zero_ne_zero).filter _

/-- Arrival-side horizontal block `H'_y = stablePart inPos C_y = W'_y ++ E'_y`. -/
def HBlock (P : Nat) (w : Nat → Bool) (y : Int) : List Nat :=
  PortInversion.stablePart (inPos w) (CList P w y)

/-- Arrival-side south block `S'_y = Q_{y-1}.filter (inDir = .south)`. -/
def SBlock (P : Nat) (w : Nat → Bool) (y : Int) : List Nat :=
  (QList P w (y - 1)).filter (fun i => decide (Drift.inDir w i = .south))

/-- Arrival-side north block `N'_y = Q_{y+1}.filter (inDir = .north)`. -/
def NBlock (P : Nat) (w : Nat → Bool) (y : Int) : List Nat :=
  (QList P w (y + 1)).filter (fun i => decide (Drift.inDir w i = .north))

theorem stablePart_outPos_QList_map_succ {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    (PortInversion.stablePart (outPos w) (QList P w y)).map (Drift.succ P) = HBlock P w y := by
  have hQneg : (QList P w y).filter (fun i => !outPos w i) =
      (QList P w y).filter (fun i => decide (Drift.outDir w i = .west)) := by
    apply List.filter_congr
    intro i hi
    rcases (QList_dirs hd hi).2 with h | h <;> simp [outPos, h]
  have hQpos : (QList P w y).filter (outPos w) =
      (QList P w y).filter (fun i => decide (Drift.outDir w i = .east)) :=
    List.filter_congr (fun i hi => outPos_QList hd hi)
  have hCneg : (CList P w y).filter (fun i => !inPos w i) =
      (CList P w y).filter (fun i => decide (Drift.inDir w i = .west)) := by
    apply List.filter_congr
    intro i hi
    rcases (CList_dirs hd hi).1 with h | h <;> simp [inPos, h]
  have hCpos : (CList P w y).filter (inPos w) =
      (CList P w y).filter (fun i => decide (Drift.inDir w i = .east)) :=
    List.filter_congr (fun i hi => inPos_CList hd hi)
  unfold HBlock PortInversion.stablePart
  rw [List.map_append, hQneg, hQpos, hCneg, hCpos]
  unfold QList CList
  rw [rankList_filter_outDir_map_succ hh hd (sameClass_move_qRep_west y),
    rankList_filter_outDir_map_succ hh hd (sameClass_move_qRep_east y)]

theorem CList_south_map_succ {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    ((CList P w y).filter (fun i => !outPos w i)).map (Drift.succ P) = SBlock P w y := by
  have hneg : (CList P w y).filter (fun i => !outPos w i) =
      (CList P w y).filter (fun i => decide (Drift.outDir w i = .south)) := by
    apply List.filter_congr
    intro i hi
    rcases (CList_dirs hd hi).2 with h | h <;> simp [outPos, h]
  rw [hneg]
  exact rankList_filter_outDir_map_succ hh hd (sameClass_move_cRep_south y)

theorem CList_north_map_succ {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    ((CList P w y).filter (outPos w)).map (Drift.succ P) = NBlock P w y := by
  have hpos : (CList P w y).filter (outPos w) =
      (CList P w y).filter (fun i => decide (Drift.outDir w i = .north)) :=
    List.filter_congr (fun i hi => outPos_CList hd hi)
  rw [hpos]
  exact rankList_filter_outDir_map_succ hh hd (sameClass_move_cRep_north y)

theorem SBlock_append_NBlock_eq_stablePart_QList {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) (y : Int) :
    SBlock P w (y + 1) ++ NBlock P w (y - 1) =
      PortInversion.stablePart (inPos w) (QList P w y) := by
  unfold SBlock NBlock PortInversion.stablePart
  rw [show y + 1 - 1 = y by omega, show y - 1 + 1 = y by omega]
  have hneg : (QList P w y).filter (fun i => !inPos w i) =
      (QList P w y).filter (fun i => decide (Drift.inDir w i = .south)) := by
    apply List.filter_congr
    intro i hi
    rcases (QList_dirs hd hi).1 with h | h <;> simp [inPos, h]
  have hpos : (QList P w y).filter (inPos w) =
      (QList P w y).filter (fun i => decide (Drift.inDir w i = .north)) :=
    List.filter_congr (fun i hi => inPos_QList hd hi)
  rw [hneg, hpos]

theorem HBlock_length {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    (HBlock P w y).length = hCnt P w y := by
  unfold HBlock
  rw [(PortInversion.stablePart_perm (inPos w) (CList P w y)).length_eq,
    CList_length_eq_hCnt hh hd y]

theorem SBlock_length {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    (SBlock P w y).length = sCnt P w y := by
  rw [← CList_south_map_succ hh hd y, List.length_map]
  have hneg : (CList P w y).filter (fun i => !outPos w i) =
      (CList P w y).filter (fun i => decide (Drift.outDir w i = .south)) := by
    apply List.filter_congr
    intro i hi
    rcases (CList_dirs hd hi).2 with h | h <;> simp [outPos, h]
  rw [hneg]
  exact ((rankList_perm_classPhases (c := cRep y) hd drift_two_zero_ne_zero).filter _).length_eq

theorem NBlock_length {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) (y : Int) :
    (NBlock P w y).length = nCnt P w y := by
  rw [← CList_north_map_succ hh hd y, List.length_map]
  have hpos : (CList P w y).filter (outPos w) =
      (CList P w y).filter (fun i => decide (Drift.outDir w i = .north)) :=
    List.filter_congr (fun i hi => outPos_CList hd hi)
  rw [hpos]
  exact ((rankList_perm_classPhases (c := cRep y) hd drift_two_zero_ne_zero).filter _).length_eq

private def rowsFrom (y0 : Int) (k : Nat) : List Int :=
  (List.range k).map (fun j : Nat => y0 + (j : Int))

private theorem depRest_flatten_eq_map_succ {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) :
    ∀ (k : Nat) (y0 : Int),
      (depRest (HBlock P w) (SBlock P w) (NBlock P w) y0 k).flatten =
        ((((((rowsFrom y0 k).map (fun y => [QList P w y, CList P w y])).flatten).map
          (PortInversion.stablePart (outPos w))).flatten).map (Drift.succ P))
  | 0, _ => by simp [depRest, rowsFrom]
  | k + 1, y0 => by
    have hrows : rowsFrom y0 (k + 1) = y0 :: rowsFrom (y0 + 1) k := by
      unfold rowsFrom
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Int.natCast_zero, Int.add_zero]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_def]
      omega
    rw [hrows]
    simp only [depRest, List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
      List.map_append]
    rw [depRest_flatten_eq_map_succ hh hd k (y0 + 1),
      stablePart_outPos_QList_map_succ hh hd y0]
    unfold PortInversion.stablePart
    rw [List.map_append, CList_south_map_succ hh hd y0, CList_north_map_succ hh hd y0,
      List.append_assoc]

private theorem arrState_flatten_eq_stablePart_inPos {P : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (2, 0)) :
    ∀ (k : Nat) (y0 : Int),
      (arrState (HBlock P w) (SBlock P w) (NBlock P w) y0 k).flatten =
        (((((rowsFrom y0 (k + 1)).map (fun y => [QList P w y, CList P w y])).flatten).map
          (PortInversion.stablePart (inPos w))).flatten)
  | 0, y0 => by
    have hrows : rowsFrom y0 1 = [y0] := by simp [rowsFrom]
    rw [hrows]
    simp only [arrState, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    rw [← List.append_assoc, SBlock_append_NBlock_eq_stablePart_QList hd y0]
    rfl
  | k + 1, y0 => by
    have hrows : rowsFrom y0 (k + 2) = y0 :: rowsFrom (y0 + 1) (k + 1) := by
      unfold rowsFrom
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Int.natCast_zero, Int.add_zero]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_def]
      omega
    rw [hrows]
    simp only [arrState, List.map_cons, List.flatten_cons, List.cons_append, List.nil_append]
    rw [arrState_flatten_eq_stablePart_inPos hd k (y0 + 1),
      ← List.append_assoc, SBlock_append_NBlock_eq_stablePart_QList hd y0]
    rfl

private theorem edge_term_mod_two (a b c : Nat) :
    ((a + (a + b) + b + (b + c)) * b) % 2 = (b + b * c) % 2 := by
  have h1 : (a + (a + b) + b + (b + c)) % 2 = (b + c) % 2 := by omega
  rw [Nat.mul_mod, h1]
  rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hb | hb <;>
    rcases (by omega : c % 2 = 0 ∨ c % 2 = 1) with hc | hc <;>
    simp [Nat.add_mod, Nat.mul_mod, hb, hc]

/-- **L18 (edge-block crossing parity `E`):**
For any kinematic word with drift `(2, 0)`, the cross-block parity `E` of the departure-to-arrival
edge-block permutation equals `∑_y (n_y + n_y * n_{y+1}) (mod 2)`. -/
theorem drift_two_zero_edge_cross_parity {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) :
    let dep3 := depRest (HBlock P w) (SBlock P w) (NBlock P w) (minY P w) (rowCount P w + 1)
    let arr3 := arrState (HBlock P w) (SBlock P w) (NBlock P w) (minY P w) (rowCount P w)
    dep3.Perm arr3 ∧
    (PortInversion.pairCross dep3 + PortInversion.pairCross arr3) % 2 =
      (((rowList P w).map (nCnt P w)).sum +
        ((rowList P w).map (fun y => nCnt P w y * nCnt P w (y + 1))).sum) % 2 := by
  intro dep3 arr3
  have hS0 : SBlock P w (minY P w) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [SBlock_length hh hd]
    exact (counts_zero_of_outside hh hd (Or.inl (Int.le_refl _))).2.2.2.1
  have hN0 : NBlock P w (minY P w - 1) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [NBlock_length hh hd]
    exact (counts_zero_of_outside hh hd (Or.inl (by omega))).2.2.2.2
  have hNend : NBlock P w (minY P w + (rowCount P w : Int)) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [NBlock_length hh hd, minY_add_rowCount]
    exact (counts_zero_of_outside hh hd (Or.inr (Int.le_refl _))).2.2.2.2
  have hSend : SBlock P w (minY P w + (rowCount P w : Int) + 1) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [SBlock_length hh hd, minY_add_rowCount]
    exact (counts_zero_of_outside hh hd (Or.inr (by omega))).2.2.2.1
  have hperm_ds := depRest_perm_depState (HBlock P w) (SBlock P w) (NBlock P w)
    (minY P w) (rowCount P w) hS0 hN0
  have hperm_sa := depState_perm_arrState (HBlock P w) (SBlock P w) (NBlock P w)
    (rowCount P w) (minY P w) hNend hSend
  have hperm : dep3.Perm arr3 := hperm_ds.trans hperm_sa
  refine ⟨hperm, ?_⟩
  have hnd_dep3 : dep3.flatten.Nodup := by
    have hflat := depRest_flatten_eq_map_succ hh hd (rowCount P w + 1) (minY P w)
    change dep3.flatten =
      (((vertexBlocks P w).map (PortInversion.stablePart (outPos w))).flatten).map (Drift.succ P) at hflat
    rw [hflat]
    have hsp_perm : (((vertexBlocks P w).map (PortInversion.stablePart (outPos w))).flatten).Perm
        (vertexBlocks P w).flatten := by
      have haux : ∀ L : List (List Nat), ((L.map (PortInversion.stablePart (outPos w))).flatten).Perm L.flatten := by
        intro L
        induction L with
        | nil => exact List.Perm.nil
        | cons b L ih =>
          simp only [List.map_cons, List.flatten_cons]
          exact (PortInversion.stablePart_perm (outPos w) b).append ih
      exact haux (vertexBlocks P w)
    have hxs1_perm : (((vertexBlocks P w).map (PortInversion.stablePart (outPos w))).flatten).Perm
        (List.range P) := hsp_perm.trans (vertexBlocks_flatten_perm_range hd)
    exact nodup_map_on' (hxs1_perm.symm.nodup List.nodup_range)
      (fun a ha b hb =>
        UnitDiagonalMatching.succ_injective
          (List.mem_range.mp (hxs1_perm.mem_iff.mp ha))
          (List.mem_range.mp (hxs1_perm.mem_iff.mp hb)))
  have hnd_state : (depState (HBlock P w) (SBlock P w) (NBlock P w) (minY P w) (rowCount P w)).flatten.Nodup :=
    hperm_ds.flatten.nodup hnd_dep3
  have hpc_eq := pairCross_depRest_eq_depState (HBlock P w) (SBlock P w) (NBlock P w)
    (minY P w) (rowCount P w) hS0 hN0
  have hslide := pairCross_depState_arrState_mod (HBlock P w) (SBlock P w) (NBlock P w)
    (rowCount P w) (minY P w) hnd_state hNend hSend
  change (PortInversion.pairCross dep3 + PortInversion.pairCross arr3) % 2 = _
  rw [show PortInversion.pairCross dep3 =
      PortInversion.pairCross (depState (HBlock P w) (SBlock P w) (NBlock P w) (minY P w) (rowCount P w))
      from hpc_eq]
  rw [hslide]
  have hmod_terms :
      ((List.range (rowCount P w)).map (fun j : Nat =>
        ((NBlock P w (minY P w + (j : Int) - 1)).length +
          (HBlock P w (minY P w + (j : Int))).length +
          (NBlock P w (minY P w + (j : Int))).length +
          (HBlock P w (minY P w + (j : Int) + 1)).length) *
        (SBlock P w (minY P w + (j : Int) + 1)).length)).sum % 2 =
      ((List.range (rowCount P w)).map (fun j : Nat =>
        nCnt P w (minY P w + (j : Int)) +
        nCnt P w (minY P w + (j : Int)) * nCnt P w (minY P w + (j : Int) + 1))).sum % 2 := by
    apply nat_sum_map_mod_congr
    intro j _
    let y : Int := minY P w + (j : Int)
    rw [NBlock_length hh hd (y - 1), HBlock_length hh hd y, NBlock_length hh hd y,
      HBlock_length hh hd (y + 1), SBlock_length hh hd (y + 1),
      hCnt_eq_nCnt_pred_add_nCnt hh hd y, hCnt_eq_nCnt_pred_add_nCnt hh hd (y + 1),
      show y + 1 - 1 = y by omega, sCnt_succ_eq_nCnt hh hd y]
    exact edge_term_mod_two (nCnt P w (y - 1)) (nCnt P w y) (nCnt P w (y + 1))
  rw [hmod_terms]
  have hlast0 : nCnt P w (minY P w + (rowCount P w : Int)) = 0 := by
    rw [minY_add_rowCount]
    exact (counts_zero_of_outside hh hd (Or.inr (Int.le_refl _))).2.2.2.2
  have hup :
      ((rowList P w).map (nCnt P w)).sum +
        ((rowList P w).map (fun y => nCnt P w y * nCnt P w (y + 1))).sum =
      ((List.range (rowCount P w)).map (fun j : Nat =>
        nCnt P w (minY P w + (j : Int)) +
        nCnt P w (minY P w + (j : Int)) * nCnt P w (minY P w + (j : Int) + 1))).sum := by
    rw [← nat_sum_map_add]
    unfold rowList
    rw [List.map_map, List.range_succ, List.map_append, nat_sum_append]
    simp only [List.map_singleton, List.sum_singleton, Function.comp_def, hlast0, Nat.zero_mul,
      Nat.add_zero]
  rw [hup]

/-- **L18 (kinematic rank parity identity, Jillhewar Eq. (20) / Ke Eq. (7)):**
For any periodic word with `(wordTrace w P).2 = .north` and `wordDrift P w = (2, 0)`,
the left-turn stable-rank sum satisfies `K ≡ 1 + P / 4 (mod 2)`. -/
theorem drift_two_zero_leftRankSum_mod_two {P : Nat} {w : Nat → Bool}
    (hh : (wordTrace w P).2 = .north) (hd : wordDrift P w = (2, 0)) :
    leftRankSum P w % 2 = (1 + P / 4) % 2 := by
  let V := vertexBlocks P w
  let xs1 := (V.map (PortInversion.stablePart (outPos w))).flatten
  let xs2 := (V.map (PortInversion.stablePart (inPos w))).flatten
  let dep3 := depRest (HBlock P w) (SBlock P w) (NBlock P w) (minY P w) (rowCount P w + 1)
  let arr3 := arrState (HBlock P w) (SBlock P w) (NBlock P w) (minY P w) (rowCount P w)
  have hsp_out := listInv_flatten_map_stablePart_mod V (vertexBlocks_nodup_each hd) (outPos w)
  have hsp_in := listInv_flatten_map_stablePart_mod V (vertexBlocks_nodup_each hd) (inPos w)
  have hdep_flat : dep3.flatten = xs1.map (Drift.succ P) :=
    depRest_flatten_eq_map_succ hh hd (rowCount P w + 1) (minY P w)
  have harr_flat : arr3.flatten = xs2 :=
    arrState_flatten_eq_stablePart_inPos hd (rowCount P w) (minY P w)
  have hxs1_perm : xs1.Perm (List.range P) := by
    have haux : ∀ L : List (List Nat), ((L.map (PortInversion.stablePart (outPos w))).flatten).Perm L.flatten := by
      intro L
      induction L with
      | nil => exact List.Perm.nil
      | cons b L ih =>
        simp only [List.map_cons, List.flatten_cons]
        exact (PortInversion.stablePart_perm (outPos w) b).append ih
    exact (haux V).trans (vertexBlocks_flatten_perm_range hd)
  have hsucc := listInv_map_succ_parity (pos_period_of_drift_two_zero hd) hxs1_perm
  have hPpos := pos_period_of_drift_two_zero hd
  have hPeven := even_period_of_north hh
  have hPodd : (P - 1) % 2 = 1 := by omega
  rw [hPodd, ← hdep_flat] at hsucc
  obtain ⟨hperm_da, hE⟩ := drift_two_zero_edge_cross_parity hh hd
  have hblocks := listInv_flatten_perm_blocks_mod hperm_da
  rw [harr_flat] at hblocks
  have hsum_wInv :
      (V.map (fun b => PortInversion.wordInv (b.map (inPos w)))).sum +
      (V.map (fun b => PortInversion.wordInv (b.map (outPos w)))).sum =
      totalWordInv P w := by
    unfold totalWordInv V
    rw [← nat_sum_map_add]
  have hL16 :
      (1 + (PortInversion.pairCross dep3 + PortInversion.pairCross arr3) + totalWordInv P w) % 2 = 0 := by
    change (PortInversion.listInv xs1 + PortInversion.listInv V.flatten) % 2 = _ at hsp_out
    change (PortInversion.listInv xs2 + PortInversion.listInv V.flatten) % 2 = _ at hsp_in
    change (PortInversion.listInv dep3.flatten + PortInversion.listInv xs2) % 2 =
      (PortInversion.pairCross dep3 + PortInversion.pairCross arr3) % 2 at hblocks
    omega
  change (PortInversion.pairCross dep3 + PortInversion.pairCross arr3) % 2 = _ at hE
  have hprod_shift :
      ((rowList P w).map (fun y => nCnt P w (y - 1) * nCnt P w y)).sum =
      ((rowList P w).map (fun y => nCnt P w y * nCnt P w (y + 1))).sum := by
    unfold rowList
    rw [List.map_map, List.map_map]
    have hstep := nat_sum_shift_eq_of_zero
      (f := fun y => nCnt P w y * nCnt P w (y + 1)) (y0 := minY P w) (m := rowCount P w)
      (by
        rw [(counts_zero_of_outside hh hd (Or.inl (by omega))).2.2.2.2]
        simp)
      (by
        rw [minY_add_rowCount, (counts_zero_of_outside hh hd (Or.inr (Int.le_refl _))).2.2.2.2]
        simp)
    refine Eq.trans ?_ hstep
    apply nat_sum_map_congr
    intro k _
    simp only [Function.comp_def]
    rw [show minY P w + (k : Int) - 1 + 1 = minY P w + (k : Int) by omega]
  have hL17 := leftRankSum_mod_two_eq_wordInv_add_prod hh hd
  have hsumN := sum_nCnt_eq_period_div_four hh hd
  omega

/-! ## 5. L19, L20, and L27: Exclusion of `g = 4` and Ke's Theorem B (`P % 8 = 4 ∧ g % 8 = 0`) -/

private theorem nat_sum_mod_two_of_all_odd {α : Type} (f : α → Nat) (xs : List α)
    (h : ∀ x ∈ xs, f x % 2 = 1) :
    (xs.map f).sum % 2 = xs.length % 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    omega

theorem leftRankSum_mod_two_eq_leftCount {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) :
    leftRankSum P w % 2 = leftCount P w % 2 := by
  unfold leftRankSum leftCount
  apply nat_sum_mod_two_of_all_odd
  intro i hi
  obtain ⟨hiR, hwi⟩ := List.mem_filter.mp hi
  have hcol := Drift.consistentWord_stableRank_color h (List.mem_range.mp hiR)
  rw [hwi] at hcol
  exact of_decide_eq_true hcol.symm

/-- **L19 (drift `(2, 0)`):** Every consistent word with drift `(2, 0)` satisfies
`P % 8 = 4` and `wordGrowth P w % 8 = 0` (and hence `wordGrowth P w ≠ 4`). -/
theorem drift_two_zero_mod_eight {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (2, 0)) :
    P % 8 = 4 ∧ wordGrowth P w % 8 = 0 := by
  have hP4 : P % 4 = 0 := period_mod_four_of_drift_two_zero h.1 hd
  have hK0 : leftRankSum P w % 2 = 0 := by
    rw [leftRankSum_mod_two_eq_leftCount h]
    exact h.leftCount_even_of_four_dvd hP4
  have hK1 : leftRankSum P w % 2 = (1 + P / 4) % 2 :=
    drift_two_zero_leftRankSum_mod_two h.1 hd
  have hP8 : P % 8 = 4 := by omega
  have hL15 := drift_two_zero_even_step_mod_four h hd
  have hg4 := h.growth_mod_four
  have hg8 : wordGrowth P w % 8 = 0 := by omega
  exact ⟨hP8, hg8⟩

theorem exists_rotate_of_twoCellAxial {v : Point} (hv : TwoCellAxialDrift v) :
    ∃ r : Direction, rotatePoint r (2, 0) = v := by
  rcases hv with ⟨h1 | h1, h2⟩ | ⟨h1, h2 | h2⟩
  · exact ⟨.north, Prod.ext (by simp [rotatePoint, h1]) (by simp [rotatePoint, h2])⟩
  · exact ⟨.south, Prod.ext (by simp [rotatePoint, h1]) (by simp [rotatePoint, h2])⟩
  · exact ⟨.west, Prod.ext (by simp [rotatePoint, h1]) (by simp [rotatePoint, h2])⟩
  · exact ⟨.east, Prod.ext (by simp [rotatePoint, h1]) (by simp [rotatePoint, h2])⟩

theorem twoCellAxial_rotatePoint (r : Direction) {v : Point} (hv : TwoCellAxialDrift v) :
    TwoCellAxialDrift (rotatePoint r v) := by
  rcases hv with ⟨h1 | h1, h2⟩ | ⟨h1, h2 | h2⟩ <;> cases r <;>
    simp [TwoCellAxialDrift, rotatePoint, h1, h2]

end TwoCellAxial

/-! ### Top-level headline theorems (L19–L20, L27) -/

/-- **L20 / L27 (Ke's Theorem B, word form):** Every consistent word with a two-cell axial full
drift `v ∈ {(±2, 0), (0, ±2)}` satisfies `P % 8 = 4` and `wordGrowth P w % 8 = 0`. -/
theorem ConsistentWord.twoCellAxial_mod_eight {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellAxialDrift (wordDrift P w)) :
    P % 8 = 4 ∧ wordGrowth P w % 8 = 0 := by
  obtain ⟨r, hr⟩ := TwoCellAxial.exists_rotate_of_twoCellAxial hd
  obtain ⟨a, haP, hdir⟩ := UnitDiagonal.ConsistentWord.exists_phase_dir h h.pos_period r
  obtain ⟨hc', hg', hd'⟩ := h.growth_shift a
  have hdir_rep : (wordTrace (repeatWord P w) a).2 = r := by
    rw [repeatWord_trace w (Nat.le_of_lt haP)]
    exact hdir
  have hd20 : wordDrift P (fun i => repeatWord P w (a + i)) = (2, 0) := by
    rw [hd', hdir_rep, ← hr, rotatePoint_inverse]
  have hmod := TwoCellAxial.drift_two_zero_mod_eight hc' hd20
  rw [hg'] at hmod
  exact hmod

/-- **L20 (growth-4 exclusion, word form):** No consistent word with a two-cell axial full drift
has growth `4`. -/
theorem ConsistentWord.twoCellAxial_growth_ne_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellAxialDrift (wordDrift P w)) :
    wordGrowth P w ≠ 4 := by
  have hg8 := (h.twoCellAxial_mod_eight hd).2
  omega

/-- Blueprint §1.2 alias for `ConsistentWord.twoCellAxial_growth_ne_four`. -/
theorem ConsistentWord.not_twoCellAxial_of_growth_four {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellAxialDrift (wordDrift P w)) :
    wordGrowth P w ≠ 4 :=
  h.twoCellAxial_growth_ne_four hd

/-- Blueprint §1.2 alias for `ConsistentWord.twoCellAxial_mod_eight`. -/
theorem ConsistentWord.twoCellAxial_period_and_growth_mod_eight {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : TwoCellAxialDrift (wordDrift P w)) :
    P % 8 = 4 ∧ wordGrowth P w % 8 = 0 :=
  h.twoCellAxial_mod_eight hd

/-- **L20 / L27 (Ke's Theorem B, periodic-tail orbit form):** Every finite-support periodic tail
with a two-cell axial full drift satisfies `P % 8 = 4` and `wordGrowth % 8 = 0`. -/
theorem periodic_tail_twoCellAxial_mod_eight {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (hv : TwoCellAxialDrift v)
    (h : HighwayFrom s T P v) :
    P % 8 = 4 ∧ wordGrowth P (fun i => readColor s (T + i)) % 8 = 0 := by
  have hc := periodic_tail_consistent_at_start hs hP h
  have hd := UnitDiagonal.wordDrift_of_highway h
  have hax : TwoCellAxialDrift (wordDrift P (fun i => readColor s (T + i))) := by
    rw [hd]
    exact TwoCellAxial.twoCellAxial_rotatePoint (inverseRotation (run s T).dir) hv
  exact hc.twoCellAxial_mod_eight hax

/-- **L20 (growth-4 exclusion, periodic-tail orbit form):** No finite-support periodic tail with a
two-cell axial full drift has growth `4`. -/
theorem periodic_tail_twoCellAxial_growth_ne_four {s : State} {T P : Nat} {v : Point}
    (hs : FiniteSupport s.board) (hP : 0 < P) (hv : TwoCellAxialDrift v)
    (h : HighwayFrom s T P v) :
    wordGrowth P (fun i => readColor s (T + i)) ≠ 4 := by
  have hg8 := (periodic_tail_twoCellAxial_mod_eight hs hP hv h).2
  omega

end LangtonsAnt
