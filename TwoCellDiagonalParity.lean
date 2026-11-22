import DriftRank
import PortInversion

/-!
# Permutation-parity bridges on `PortInversion` for two-cell diagonal quotients

Pure list combinatorics extending `PortInversion` (no `sorry`, no `axiom`, no `native_decide`):

1. `listInv_map_succ_parity`: applying the cyclic shift `Drift.succ P` to any permutation `xs`
   of `List.range P` flips `PortInversion.listInv` by `(P - 1) mod 2`.
2. `crossInv_add_symm_of_disjoint` & `pairCross_perm_parity`: for pairwise-disjoint blocks,
   `pairCross (srcOrder.map blk) + pairCross (dstOrder.map blk)` agrees mod 2 with the
   weighted block-inversion count `edgePairInv dstLt (fun e => (blk e).length) srcOrder`.
3. `pairInvSum`, `crossInvSum`, `edgePairInv_eq_pairInvSum`, `pairInvSum_perm_on`,
   `pairInvSum_mod_two_congr`, and `const_wt` / zero-vanishing helpers.
4. `eq_of_perm_of_pairwise_lt` and `rankSum_map_range` for rank-sorted class blocks.
-/

namespace LangtonsAnt
namespace TwoCellDiagonal

/-! ## 1. Cyclic shift parity for `Drift.succ P` -/

private theorem filter_lt_map_add_one (xs : List Nat) (x : Nat) :
    ((xs.map (· + 1)).filter (fun y => y < x + 1)).length =
      (xs.filter (fun y => y < x)).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a < x
    · have h1 : a + 1 < x + 1 := by omega
      simp [h, h1, ih]
    · have h1 : ¬ (a + 1 < x + 1) := by omega
      simp [h, h1, ih]

private theorem listInv_map_add_one (xs : List Nat) :
    PortInversion.listInv (xs.map (· + 1)) = PortInversion.listInv xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, PortInversion.listInv_cons, filter_lt_map_add_one, ih]

private theorem crossInv_map_add_one (xs ys : List Nat) :
    PortInversion.crossInv (xs.map (· + 1)) (ys.map (· + 1)) = PortInversion.crossInv xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, PortInversion.crossInv_cons, filter_lt_map_add_one, ih]

private theorem map_succ_eq_add_one {P : Nat} {xs : List Nat}
    (hlt : ∀ a ∈ xs, a + 1 < P) :
    xs.map (Drift.succ P) = xs.map (· + 1) := by
  apply List.map_congr_left
  intro a ha
  exact Nat.mod_eq_of_lt (hlt a ha)

/-- Applying the cyclic shift `Drift.succ P` to any permutation `xs` of `List.range P`
flips `listInv` by `(P - 1) mod 2` (hence by `1 mod 2` for every even `P > 0`). -/
theorem listInv_map_succ_parity {P : Nat} {xs : List Nat} (hP : 0 < P)
    (hperm : xs.Perm (List.range P)) :
    (PortInversion.listInv (xs.map (Drift.succ P)) + PortInversion.listInv xs) % 2 = (P - 1) % 2 := by
  have hmem : P - 1 ∈ xs := hperm.mem_iff.mpr (List.mem_range.mpr (by omega))
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  have hnd : (pre ++ (P - 1) :: post).Nodup := hperm.symm.nodup List.nodup_range
  have hlen : pre.length + post.length + 1 = P := by
    have hl := hperm.length_eq
    simp only [List.length_append, List.length_cons, List.length_range] at hl
    omega
  have hlt_pre : ∀ a ∈ pre, a + 1 < P := by
    intro a ha
    have haP : a < P := List.mem_range.mp (hperm.mem_iff.mp (by simp [ha]))
    have hne : a ≠ P - 1 := by
      intro he; subst he
      exact (List.nodup_append.mp hnd).2.2 (P - 1) ha (P - 1) (by simp) rfl
    omega
  have hlt_post : ∀ a ∈ post, a + 1 < P := by
    intro a ha
    have haP : a < P := List.mem_range.mp (hperm.mem_iff.mp (by simp [ha]))
    have hne : a ≠ P - 1 := by
      intro he; subst he
      exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 ha
    omega
  have hsucc_last : Drift.succ P (P - 1) = 0 := by
    change (P - 1 + 1) % P = 0
    rw [show P - 1 + 1 = P by omega, Nat.mod_self]
  have hmap :
      (pre ++ (P - 1) :: post).map (Drift.succ P) =
        pre.map (· + 1) ++ 0 :: post.map (· + 1) := by
    rw [List.map_append, List.map_cons, hsucc_last,
      map_succ_eq_add_one hlt_pre, map_succ_eq_add_one hlt_post]
  have hinv_orig :
      PortInversion.listInv (pre ++ (P - 1) :: post) =
        PortInversion.listInv pre + PortInversion.listInv post +
          PortInversion.crossInv pre post + post.length := by
    rw [PortInversion.listInv_append, PortInversion.listInv_cons,
      PortInversion.crossInv_cons_right, PortInversion.crossInv_singleton_right]
    have hpre_zero : pre.filter (fun u => P - 1 < u) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha; have := hlt_pre a ha; simp; omega
    have hpost_all : post.filter (fun y => y < P - 1) = post := by
      rw [List.filter_eq_self]
      intro a ha; have := hlt_post a ha; simp; omega
    rw [hpre_zero, hpost_all, List.length_nil]; omega
  have hinv_map :
      PortInversion.listInv (pre.map (· + 1) ++ 0 :: post.map (· + 1)) =
        PortInversion.listInv pre + PortInversion.listInv post +
          PortInversion.crossInv pre post + pre.length := by
    rw [PortInversion.listInv_append, PortInversion.listInv_cons,
      PortInversion.crossInv_cons_right, PortInversion.crossInv_singleton_right,
      listInv_map_add_one, listInv_map_add_one, crossInv_map_add_one]
    have hpre_all : (pre.map (· + 1)).filter (fun u => 0 < u) = pre.map (· + 1) := by
      rw [List.filter_eq_self]
      intro a ha; obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha; simp
    have hpost_zero : (post.map (· + 1)).filter (fun y => y < 0) = [] := by
      rw [List.filter_eq_nil_iff]; intro a _; simp
    rw [hpre_all, hpost_zero, List.length_map, List.length_nil]; omega
  rw [hmap, hinv_map, hinv_orig]; omega

/-! ## 2. Block-permutation cross-inversion parity -/

private theorem crossInv_perm_right (xs : List Nat) {ys1 ys2 : List Nat} (h : ys1.Perm ys2) :
    PortInversion.crossInv xs ys1 = PortInversion.crossInv xs ys2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [PortInversion.crossInv_cons, (h.filter _).length_eq, ih]

/-- For disjoint lists `xs` and `ys`, `crossInv xs ys + crossInv ys xs = xs.length * ys.length`. -/
theorem crossInv_add_symm_of_disjoint {xs ys : List Nat} (hdisj : ∀ a ∈ xs, a ∉ ys) :
    PortInversion.crossInv xs ys + PortInversion.crossInv ys xs = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have htri := PortInversion.filter_lt_add_filter_gt x ys (hdisj x (by simp))
    have hstep := ih (fun a ha => hdisj a (by simp [ha]))
    rw [PortInversion.crossInv_cons, PortInversion.crossInv_cons_right,
      PortInversion.crossInv_singleton_right, List.length_cons, Nat.succ_mul]
    omega

private theorem pairCross_append (as bs : List (List Nat)) :
    PortInversion.pairCross (as ++ bs) =
      PortInversion.pairCross as + PortInversion.pairCross bs +
        PortInversion.crossInv as.flatten bs.flatten := by
  induction as with
  | nil => simp [PortInversion.pairCross]
  | cons a as ih =>
    simp only [List.cons_append, PortInversion.pairCross, List.flatten_append,
      PortInversion.crossInv_append_right, List.flatten_cons, PortInversion.crossInv_append_left, ih]
    omega

private theorem pairCross_append_cons (as : List (List Nat)) (b : List Nat) (cs : List (List Nat)) :
    PortInversion.pairCross (as ++ b :: cs) =
      PortInversion.pairCross (as ++ cs) +
        PortInversion.crossInv as.flatten b + PortInversion.crossInv b cs.flatten := by
  rw [pairCross_append, pairCross_append]
  simp only [PortInversion.pairCross, List.flatten_cons, PortInversion.crossInv_append_right]
  omega

/-- Weighted inversion count along a source-ordered list relative to a target comparison `dstLt`. -/
def edgePairInv {ι : Type} (dstLt : ι → ι → Bool) (wt : ι → Nat) : List ι → Nat
  | [] => 0
  | e :: es =>
      (es.map (fun e' => if dstLt e' e then wt e * wt e' else 0)).sum +
        edgePairInv dstLt wt es

/-- Symmetric weighted pair-inversion count between two strict orderings `srcLt` and `dstLt`. -/
def pairInvSum {ι : Type} (srcLt dstLt : ι → ι → Bool) (wt : ι → Nat) : List ι → Nat
  | [] => 0
  | e :: es =>
      (es.map (fun e' => if srcLt e e' != dstLt e e' then wt e * wt e' else 0)).sum +
        pairInvSum srcLt dstLt wt es

/-- Weighted cross-inversion count between two disjoint lists `xs` and `ys`. -/
def crossInvSum {ι : Type} (srcLt dstLt : ι → ι → Bool) (wt : ι → Nat) (xs ys : List ι) : Nat :=
  (xs.map (fun x =>
    (ys.map (fun y => if srcLt x y != dstLt x y then wt x * wt y else 0)).sum)).sum

private theorem edgePairInv_append_cons {ι : Type} (dstLt : ι → ι → Bool) (wt : ι → Nat)
    (pre post : List ι) (d : ι)
    (hpre : ∀ e ∈ pre, dstLt d e = true)
    (hpost : ∀ e ∈ post, dstLt e d = false) :
    edgePairInv dstLt wt (pre ++ d :: post) =
      edgePairInv dstLt wt (pre ++ post) + (pre.map (fun e => wt e * wt d)).sum := by
  induction pre with
  | nil =>
    simp only [List.nil_append, edgePairInv, List.map_nil, List.sum_nil, Nat.add_zero]
    have hzero : (post.map (fun e' => if dstLt e' d then wt d * wt e' else 0)).sum = 0 := by
      induction post with
      | nil => simp
      | cons y ys iys =>
        simp only [List.map_cons, List.sum_cons, hpost y (by simp), Bool.false_eq_true, ite_false,
          Nat.zero_add]
        exact iys (fun e he => hpost e (by simp [he]))
    rw [hzero, Nat.zero_add]
  | cons x xs ih =>
    have hx : dstLt d x = true := hpre x (by simp)
    have hxs := ih (fun e he => hpre e (by simp [he]))
    simp only [List.cons_append, edgePairInv, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, hx, ite_true] at hxs ⊢
    omega

private theorem sum_map_mul_right {ι : Type} (f : ι → Nat) (c : Nat) (xs : List ι) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

private theorem flatten_length_map {ι : Type} (blk : ι → List Nat) (xs : List ι) :
    (xs.map blk).flatten.length = (xs.map (fun e => (blk e).length)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons, ih]

theorem perm_flatten_map {ι : Type} (blk : ι → List Nat) {xs ys : List ι}
    (h : xs.Perm ys) : (xs.map blk).flatten.Perm (ys.map blk).flatten := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih => simp only [List.map_cons, List.flatten_cons]; exact ih.append_left (blk x)
  | swap x y l =>
    simp only [List.map_cons, List.flatten_cons]
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Block-permutation cross-inversion parity:** For any two permutations `srcOrder` and
`dstOrder` of pairwise-disjoint `Nat` blocks (with `dstOrder` strictly increasing in `dstLt`),
`pairCross (srcOrder.map blk) + pairCross (dstOrder.map blk)` has the same parity as
`edgePairInv dstLt (fun e => (blk e).length) srcOrder`. -/
theorem pairCross_perm_parity {ι : Type} (dstLt : ι → ι → Bool) (blk : ι → List Nat) :
    ∀ (dstOrder srcOrder : List ι),
      srcOrder.Perm dstOrder →
      dstOrder.Nodup →
      dstOrder.Pairwise (fun a b => dstLt a b = true) →
      (∀ a ∈ dstOrder, ∀ b ∈ dstOrder, dstLt a b = true → dstLt b a = false) →
      (dstOrder.map blk).flatten.Nodup →
      (PortInversion.pairCross (srcOrder.map blk) + PortInversion.pairCross (dstOrder.map blk)) % 2 =
        edgePairInv dstLt (fun e => (blk e).length) srcOrder % 2
  | [], srcOrder, hperm, _, _, _, _ => by
    have hnil : srcOrder = [] := (List.Perm.nil_eq hperm.symm).symm
    subst hnil; rfl
  | d :: ds, srcOrder, hperm, hnd, hpw, hasym, hflat_nd => by
    have hd_mem : d ∈ srcOrder := hperm.mem_iff.mpr (by simp)
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hd_mem
    have hperm_rest : (pre ++ post).Perm ds := (List.perm_middle.symm.trans hperm).cons_inv
    obtain ⟨_, hnd_ds⟩ := List.nodup_cons.mp hnd
    obtain ⟨hd_lt_ds, hpw_ds⟩ := List.pairwise_cons.mp hpw
    have hasym_ds : ∀ a ∈ ds, ∀ b ∈ ds, dstLt a b = true → dstLt b a = false :=
      fun a ha b hb => hasym a (by simp [ha]) b (by simp [hb])
    simp only [List.map_cons, List.flatten_cons] at hflat_nd
    obtain ⟨_, hflat_ds_nd, hdisj_d_ds⟩ := List.nodup_append.mp hflat_nd
    have ih := pairCross_perm_parity dstLt blk ds (pre ++ post) hperm_rest hnd_ds hpw_ds
      hasym_ds hflat_ds_nd
    have hpre_lt : ∀ e ∈ pre, dstLt d e = true := fun e he =>
      hd_lt_ds e (hperm_rest.mem_iff.mp (by simp [he]))
    have hpost_gt : ∀ e ∈ post, dstLt e d = false := fun e he =>
      let heds := hperm_rest.mem_iff.mp (by simp [he])
      hasym d (by simp) e (by simp [heds]) (hd_lt_ds e heds)
    have hdisj_pre : ∀ a ∈ (pre.map blk).flatten, a ∉ blk d := by
      intro a ha had
      have ha_ds : a ∈ (ds.map blk).flatten :=
        (perm_flatten_map blk hperm_rest).mem_iff.mp (by
          rw [List.map_append, List.flatten_append]; exact List.mem_append_left _ ha)
      exact hdisj_d_ds a had a ha_ds rfl
    have hsym := crossInv_add_symm_of_disjoint hdisj_pre
    rw [flatten_length_map] at hsym
    have hpc_dst :
        PortInversion.pairCross ((d :: ds).map blk) =
          PortInversion.crossInv (blk d) (pre.map blk).flatten +
            PortInversion.crossInv (blk d) (post.map blk).flatten +
            PortInversion.pairCross (ds.map blk) := by
      simp only [List.map_cons, PortInversion.pairCross]
      rw [crossInv_perm_right (blk d) (perm_flatten_map blk hperm_rest.symm),
        List.map_append, List.flatten_append, PortInversion.crossInv_append_right]
    have hpc_src :
        PortInversion.pairCross ((pre ++ d :: post).map blk) =
          PortInversion.pairCross ((pre ++ post).map blk) +
            PortInversion.crossInv (pre.map blk).flatten (blk d) +
            PortInversion.crossInv (blk d) (post.map blk).flatten := by
      rw [List.map_append, List.map_cons, pairCross_append_cons, ← List.map_append]
    have hepi := edgePairInv_append_cons dstLt (fun e => (blk e).length) pre post d hpre_lt hpost_gt
    rw [sum_map_mul_right] at hepi
    rw [hpc_src, hpc_dst, hepi]
    omega

/-! ## 3. Permutation invariance and algebra of `pairInvSum` / `crossInvSum` -/

theorem edgePairInv_eq_pairInvSum {ι : Type} (srcLt dstLt : ι → ι → Bool) (wt : ι → Nat) :
    ∀ xs : List ι,
      xs.Nodup →
      xs.Pairwise (fun a b => srcLt a b = true) →
      (∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → dstLt b a = !dstLt a b) →
      edgePairInv dstLt wt xs = pairInvSum srcLt dstLt wt xs
  | [], _, _, _ => rfl
  | x :: xs, hnd, hpw, htot => by
    obtain ⟨hxnot, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hxlt, hpw'⟩ := List.pairwise_cons.mp hpw
    have ih := edgePairInv_eq_pairInvSum srcLt dstLt wt xs hnd' hpw'
      (fun a ha b hb => htot a (by simp [ha]) b (by simp [hb]))
    simp only [edgePairInv, pairInvSum, ih]
    congr 1; congr 1
    apply List.map_congr_left
    intro y hy
    have hs : srcLt x y = true := hxlt y hy
    have hd : dstLt y x = !dstLt x y := htot x (by simp) y (by simp [hy]) (fun h => hxnot (h ▸ hy))
    rw [hs, hd]
    cases dstLt x y <;> simp

private theorem pairInvSum_perm_aux {ι : Type} (srcLt dstLt : ι → ι → Bool) (wt : ι → Nat)
    (hsym : ∀ a b, (srcLt a b != dstLt a b) = (srcLt b a != dstLt b a))
    {xs ys : List ι} (h : xs.Perm ys) :
    pairInvSum srcLt dstLt wt xs = pairInvSum srcLt dstLt wt ys := by
  induction h with
  | nil => rfl
  | cons x hp ih => simp only [pairInvSum, ih, PortInversion.perm_sum (hp.map _)]
  | swap x y l =>
    simp only [pairInvSum, List.map_cons, List.sum_cons, hsym x y, Nat.mul_comm (wt y) (wt x)]
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem pairInvSum_perm_on {ι : Type} (srcLt dstLt : ι → ι → Bool) (wt : ι → Nat)
    {P : ι → Prop} [DecidablePred P]
    (hsym : ∀ a b, P a → P b → (srcLt a b != dstLt a b) = (srcLt b a != dstLt b a))
    {xs ys : List ι} (h : xs.Perm ys) (hP : ∀ a ∈ xs, P a) :
    pairInvSum srcLt dstLt wt xs = pairInvSum srcLt dstLt wt ys := by
  let srcLt' : ι → ι → Bool := fun a b => if P a ∧ P b then srcLt a b else false
  let dstLt' : ι → ι → Bool := fun a b => if P a ∧ P b then dstLt a b else false
  have hsym' : ∀ a b, (srcLt' a b != dstLt' a b) = (srcLt' b a != dstLt' b a) := by
    intro a b
    by_cases hab : P a ∧ P b
    · have hba : P b ∧ P a := ⟨hab.2, hab.1⟩
      dsimp only [srcLt', dstLt']
      rw [ite_eq_left hab, ite_eq_left hab, ite_eq_left hba, ite_eq_left hba]
      exact hsym a b hab.1 hab.2
    · have hba : ¬ (P b ∧ P a) := fun ⟨hb, ha⟩ => hab ⟨ha, hb⟩
      dsimp only [srcLt', dstLt']
      rw [ite_eq_right hab, ite_eq_right hab, ite_eq_right hba, ite_eq_right hba]
  have hEq : ∀ zs : List ι, (∀ a ∈ zs, P a) →
      pairInvSum srcLt dstLt wt zs = pairInvSum srcLt' dstLt' wt zs := by
    intro zs hzs
    induction zs with
    | nil => rfl
    | cons z zs izs =>
      simp only [pairInvSum, izs (fun a ha => hzs a (by simp [ha]))]
      congr 1; congr 1
      apply List.map_congr_left
      intro b hb
      have hz : P z := hzs z (by simp)
      have hb' : P b := hzs b (by simp [hb])
      simp [srcLt', dstLt', hz, hb']
  rw [hEq xs hP, hEq ys (fun a ha => hP a (h.mem_iff.mpr ha))]
  exact pairInvSum_perm_aux srcLt' dstLt' wt hsym' h

theorem pairInvSum_append {ι : Type} (srcLt dstLt : ι → ι → Bool) (wt : ι → Nat)
    (xs ys : List ι) :
    pairInvSum srcLt dstLt wt (xs ++ ys) =
      pairInvSum srcLt dstLt wt xs + pairInvSum srcLt dstLt wt ys +
        crossInvSum srcLt dstLt wt xs ys := by
  induction xs with
  | nil => simp [pairInvSum, crossInvSum]
  | cons x xs ih =>
    simp only [List.cons_append, pairInvSum, crossInvSum, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]
    omega

theorem crossInvSum_append_left {ι : Type} (srcLt dstLt : ι → ι → Bool) (wt : ι → Nat)
    (xs1 xs2 ys : List ι) :
    crossInvSum srcLt dstLt wt (xs1 ++ xs2) ys =
      crossInvSum srcLt dstLt wt xs1 ys + crossInvSum srcLt dstLt wt xs2 ys := by
  simp [crossInvSum, List.map_append, List.sum_append]

theorem crossInvSum_append_right {ι : Type} (srcLt dstLt : ι → ι → Bool) (wt : ι → Nat)
    (xs ys1 ys2 : List ι) :
    crossInvSum srcLt dstLt wt xs (ys1 ++ ys2) =
      crossInvSum srcLt dstLt wt xs ys1 + crossInvSum srcLt dstLt wt xs ys2 := by
  induction xs with
  | nil => simp [crossInvSum]
  | cons x xs ih =>
    simp only [crossInvSum, List.map_cons, List.sum_cons, List.map_append, List.sum_append] at ih ⊢
    omega

theorem nat_sum_map_mod_two_congr {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x % 2 = g x % 2) :
    (xs.map f).sum % 2 = (xs.map g).sum % 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    omega

theorem pairInvSum_mod_two_congr {ι : Type} (srcLt dstLt : ι → ι → Bool)
    (wt1 wt2 : ι → Nat) (xs : List ι) (h : ∀ e ∈ xs, wt1 e % 2 = wt2 e % 2) :
    pairInvSum srcLt dstLt wt1 xs % 2 = pairInvSum srcLt dstLt wt2 xs % 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [pairInvSum]
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    have hrow :
        (xs.map (fun e' => if srcLt x e' != dstLt x e' then wt1 x * wt1 e' else 0)).sum % 2 =
        (xs.map (fun e' => if srcLt x e' != dstLt x e' then wt2 x * wt2 e' else 0)).sum % 2 := by
      apply nat_sum_map_mod_two_congr
      intro y hy
      split
      · rw [Nat.mul_mod, hx, h y (by simp [hy]), ← Nat.mul_mod]
      · rfl
    omega

theorem pairInvSum_const_wt {ι : Type} (srcLt dstLt : ι → ι → Bool)
    (wt : ι → Nat) (c : Nat) (xs : List ι) (h : ∀ e ∈ xs, wt e = c) :
    pairInvSum srcLt dstLt wt xs = pairInvSum srcLt dstLt (fun _ => 1) xs * (c * c) := by
  induction xs with
  | nil => simp [pairInvSum]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    have hrow :
        (xs.map (fun e' => if srcLt x e' != dstLt x e' then wt x * wt e' else 0)).sum =
        (xs.map (fun e' => if srcLt x e' != dstLt x e' then 1 * 1 else 0)).sum * (c * c) := by
      rw [← sum_map_mul_right]
      congr 1; apply List.map_congr_left
      intro y hy; rw [hx, h y (by simp [hy])]; split <;> simp
    simp only [pairInvSum, hrow, hxs, Nat.add_mul]

theorem crossInvSum_const_wt {ι : Type} (srcLt dstLt : ι → ι → Bool)
    (wt : ι → Nat) (c1 c2 : Nat) (xs ys : List ι)
    (hx : ∀ e ∈ xs, wt e = c1) (hy : ∀ e ∈ ys, wt e = c2) :
    crossInvSum srcLt dstLt wt xs ys =
      crossInvSum srcLt dstLt (fun _ => 1) xs ys * (c1 * c2) := by
  induction xs with
  | nil => simp [crossInvSum]
  | cons x xs ih =>
    have hx0 := hx x (by simp)
    have hxs := ih (fun e he => hx e (by simp [he]))
    have hrow :
        (ys.map (fun y => if srcLt x y != dstLt x y then wt x * wt y else 0)).sum =
        (ys.map (fun y => if srcLt x y != dstLt x y then 1 * 1 else 0)).sum * (c1 * c2) := by
      rw [← sum_map_mul_right]
      congr 1; apply List.map_congr_left
      intro y hy'; rw [hx0, hy y hy']; split <;> simp
    simp only [crossInvSum, List.map_cons, List.sum_cons] at hxs ⊢
    rw [hrow, hxs, Nat.add_mul]

theorem crossInvSum_eq_zero_of_all_false {ι : Type} (srcLt dstLt : ι → ι → Bool)
    (wt : ι → Nat) (xs ys : List ι)
    (h0 : ∀ x ∈ xs, ∀ y ∈ ys, (srcLt x y != dstLt x y) = false) :
    crossInvSum srcLt dstLt wt xs ys = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [crossInvSum, List.map_cons, List.sum_cons]
    have hrow : ∀ zs : List ι, (∀ y ∈ zs, (srcLt x y != dstLt x y) = false) →
        (zs.map (fun y => if srcLt x y != dstLt x y then wt x * wt y else 0)).sum = 0 := by
      intro zs hzs
      induction zs with
      | nil => rfl
      | cons y ys iys =>
        simp only [List.map_cons, List.sum_cons, hzs y (by simp), Bool.false_eq_true, ite_false,
          Nat.zero_add]
        exact iys (fun b hb => hzs b (by simp [hb]))
    rw [hrow ys (h0 x (by simp)), Nat.zero_add]
    exact ih (fun a ha b hb => h0 a (by simp [ha]) b hb)

private theorem le_sum_of_mem_nat {a : Nat} {xs : List Nat} (h : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · omega
    · have := ih hmem; omega

theorem crossInvSum_eq_zero_of_unit_eq_zero {ι : Type} (srcLt dstLt : ι → ι → Bool)
    (wt : ι → Nat) (xs ys : List ι)
    (h0 : crossInvSum srcLt dstLt (fun _ => 1) xs ys = 0) :
    crossInvSum srcLt dstLt wt xs ys = 0 := by
  apply crossInvSum_eq_zero_of_all_false
  intro x hx y hy
  by_cases hc : (srcLt x y != dstLt x y) = false
  · exact hc
  · exfalso
    have hct : (srcLt x y != dstLt x y) = true := by cases h : (srcLt x y != dstLt x y) <;> simp_all
    have hpos_row : 1 ≤ (ys.map (fun b => if srcLt x b != dstLt x b then 1 * 1 else 0)).sum :=
      le_sum_of_mem_nat (List.mem_map.mpr ⟨y, hy, by simp [hct]⟩)
    have hpos : 1 ≤ crossInvSum srcLt dstLt (fun _ => 1) xs ys := by
      unfold crossInvSum
      have hle : (ys.map (fun b => if srcLt x b != dstLt x b then 1 * 1 else 0)).sum ≤
          (xs.map (fun a => (ys.map (fun b => if srcLt a b != dstLt a b then 1 * 1 else 0)).sum)).sum :=
        le_sum_of_mem_nat (List.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Nat.le_trans hpos_row hle
    omega

/-! ## 4. Sorted list uniqueness and `PortInversion.rankSum` bridge -/

theorem eq_of_perm_of_pairwise_lt {α : Type} (r : α → Nat) :
    ∀ {xs ys : List α},
      xs.Perm ys →
      xs.Pairwise (fun a b => r a < r b) →
      ys.Pairwise (fun a b => r a < r b) →
      xs = ys
  | [], ys, hperm, _, _ => List.Perm.nil_eq hperm
  | x :: xs, [], hperm, _, _ => (List.Perm.nil_eq hperm.symm).symm
  | x :: xs, y :: ys, hperm, hx, hy => by
    obtain ⟨hxlt, hxs⟩ := List.pairwise_cons.mp hx
    obtain ⟨hylt, hys⟩ := List.pairwise_cons.mp hy
    have hxy : x = y := by
      by_cases he : x = y
      · exact he
      · exfalso
        have hx_in : x ∈ ys := by
          rcases List.mem_cons.mp (hperm.mem_iff.mp List.mem_cons_self) with h1 | h2
          · exact False.elim (he h1)
          · exact h2
        have hy_in : y ∈ xs := by
          rcases List.mem_cons.mp (hperm.mem_iff.mpr List.mem_cons_self) with h1 | h2
          · exact False.elim (he h1.symm)
          · exact h2
        have h1 := hylt x hx_in
        have h2 := hxlt y hy_in
        omega
    subst hxy
    congr 1
    exact eq_of_perm_of_pairwise_lt r hperm.cons_inv hxs hys

private theorem countTrue_append_singleton (α : List Bool) (b : Bool) :
    PortInversion.countTrue (α ++ [b]) = PortInversion.countTrue α + if b then 1 else 0 := by
  induction α with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [PortInversion.countTrue] at ih ⊢ <;> omega

private theorem rankSum_append_singleton (α : List Bool) (b : Bool) :
    PortInversion.rankSum (α ++ [b]) =
      PortInversion.rankSum α + if b then α.length else 0 := by
  induction α with
  | nil => cases b <;> rfl
  | cons a l ih =>
    simp only [List.cons_append, PortInversion.rankSum, ih, countTrue_append_singleton,
      List.length_cons]
    cases b <;> simp <;> omega

theorem rankSum_map_range (g : Nat → Nat) (p : Nat → Bool) (n : Nat) :
    PortInversion.rankSum (((List.range n).map g).map p) =
      ((List.range n).filter (fun k => p (g k))).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton,
      rankSum_append_singleton, ih, List.length_map, List.length_map, List.length_range,
      List.filter_append, List.sum_append]
    cases hp : p (g n) <;> simp [hp]

end TwoCellDiagonal
end LangtonsAnt
