import TwoCellDiagonalParity

/-!
# The `(2, -2)` quotient edge set, 4-edge gadget parity table, and window edge orders

Pure combinatorial model of the `(2, -2)` two-lane directed quotient graph and the 4-edge
gadgets `G^C_{j, r}` (blueprint item **L23**, zero `sorry`, zero `axiom`, zero `native_decide`):

1. `GEdge` (`N/W/E/S` edges indexed by their unique owning gadget `(j, r)`), lexicographic
   `(layer, lane, port)` orders `edgeSrcLt` and `edgeDstLt`, shift invariance, injectivity
   on odd-`j` edges, and symmetry of the inversion indicator `edgeSrcLt != edgeDstLt`.
2. The 4-edge gadget parity table:
   - `gadget_self_inv_eq_three` (`3 ≡ 1 mod 2`),
   - `gadget_cross_same_layer_eq_eight` (`8 ≡ 0 mod 2`),
   - `gadget_cross_step_two_mod_two` (`1` iff `r1 = r2`, else `0` or `2 ≡ 0 mod 2`),
   - `gadget_cross_ge_four_eq_zero` (`0` for `j1 + 4 ≤ j2`),
   - `gadgetStack_pairInvSum_mod_two` (`E % 2 = ∑_{r, k} (n + n·n') % 2`).
3. Window vertex/edge orderings `windowVertices`, `windowSrcOrder`, `windowDstOrder`, pairwise
   strict order proofs, and exact permutations with `gadgetStack`.
-/

namespace LangtonsAnt
namespace TwoCellDiagonal

/-! ## 1. Quotient edges `GEdge` and lexicographic `(layer, lane, port)` orders -/

/-- The four directed edge types inside a two-lane gadget `G^C_{j, r}`. -/
inductive GEdgeKind where
  | N | W | E | S
  deriving DecidableEq, Repr

/-- A directed quotient edge of the `(2, -2)` graph, indexed by its unique owning gadget
`(j, r)` (`j` odd, `r : Bool`) and edge kind `N/W/E/S`. -/
structure GEdge where
  j : Int
  r : Bool
  kind : GEdgeKind
  deriving DecidableEq, Repr

def GEdge.srcLayer (e : GEdge) : Int :=
  match e.kind with | .N => e.j | .W => e.j + 1 | .E => e.j + 1 | .S => e.j + 2

def GEdge.srcLane (e : GEdge) : Bool :=
  match e.kind with | .N => e.r | .W => !e.r | .E => !e.r | .S => e.r

def GEdge.srcPort (e : GEdge) : Bool :=
  match e.kind with | .N => true | .W => false | .E => true | .S => false

def GEdge.dstLayer (e : GEdge) : Int :=
  match e.kind with | .N => e.j + 1 | .W => e.j | .E => e.j + 2 | .S => e.j + 1

def GEdge.dstLane (e : GEdge) : Bool := e.r

def GEdge.dstPort (e : GEdge) : Bool :=
  match e.kind with | .N => true | .W => false | .E => true | .S => false

def GEdge.dir (e : GEdge) : Direction :=
  match e.kind with | .N => .north | .W => .west | .E => .east | .S => .south

def GEdge.srcKey (e : GEdge) : Int × Bool × Bool := (e.srcLayer, e.srcLane, e.srcPort)
def GEdge.dstKey (e : GEdge) : Int × Bool × Bool := (e.dstLayer, e.dstLane, e.dstPort)
def GEdge.shift (d : Int) (e : GEdge) : GEdge := ⟨e.j + d, e.r, e.kind⟩

/-- Strict lexicographic order on `(layer, lane, port)` (`false < true`). -/
def keyLt (a b : Int × Bool × Bool) : Bool :=
  if a.1 < b.1 then true
  else if b.1 < a.1 then false
  else if a.2.1 != b.2.1 then !a.2.1
  else (!a.2.2) && b.2.2

def edgeSrcLt (e1 e2 : GEdge) : Bool := keyLt e1.srcKey e2.srcKey
def edgeDstLt (e1 e2 : GEdge) : Bool := keyLt e1.dstKey e2.dstKey

private theorem keyLt_irrefl (a : Int × Bool × Bool) : keyLt a a = false := by
  rcases a with ⟨t, r, p⟩
  unfold keyLt
  cases r <;> cases p <;> simp

private theorem keyLt_total {a b : Int × Bool × Bool} (hne : a ≠ b) :
    keyLt b a = !keyLt a b := by
  rcases a with ⟨t1, r1, p1⟩
  rcases b with ⟨t2, r2, p2⟩
  unfold keyLt
  by_cases h1 : t1 < t2
  · have h2 : ¬ (t2 < t1) := by omega
    simp [h1, h2]
  · by_cases h2 : t2 < t1
    · simp [h1, h2]
    · have ht : t1 = t2 := by omega
      subst ht
      simp only [Int.lt_irrefl, ite_false]
      cases r1 <;> cases r2 <;> cases p1 <;> cases p2 <;> simp_all

private theorem keyLt_shift (d : Int) (a b : Int × Bool × Bool) :
    keyLt (a.1 + d, a.2.1, a.2.2) (b.1 + d, b.2.1, b.2.2) = keyLt a b := by
  rcases a with ⟨t1, r1, p1⟩
  rcases b with ⟨t2, r2, p2⟩
  unfold keyLt
  have h1 : (t1 + d < t2 + d) ↔ (t1 < t2) := by omega
  have h2 : (t2 + d < t1 + d) ↔ (t2 < t1) := by omega
  simp [h1, h2]

private theorem edgeSrcLt_shift (d : Int) (e1 e2 : GEdge) :
    edgeSrcLt (e1.shift d) (e2.shift d) = edgeSrcLt e1 e2 := by
  unfold edgeSrcLt
  have h1 : (e1.shift d).srcKey = (e1.srcKey.1 + d, e1.srcKey.2.1, e1.srcKey.2.2) := by
    rcases e1 with ⟨j, r, k⟩
    cases k <;> simp [GEdge.shift, GEdge.srcKey, GEdge.srcLayer, GEdge.srcLane, GEdge.srcPort] <;> omega
  have h2 : (e2.shift d).srcKey = (e2.srcKey.1 + d, e2.srcKey.2.1, e2.srcKey.2.2) := by
    rcases e2 with ⟨j, r, k⟩
    cases k <;> simp [GEdge.shift, GEdge.srcKey, GEdge.srcLayer, GEdge.srcLane, GEdge.srcPort] <;> omega
  rw [h1, h2, keyLt_shift]

private theorem edgeDstLt_shift (d : Int) (e1 e2 : GEdge) :
    edgeDstLt (e1.shift d) (e2.shift d) = edgeDstLt e1 e2 := by
  unfold edgeDstLt
  have h1 : (e1.shift d).dstKey = (e1.dstKey.1 + d, e1.dstKey.2.1, e1.dstKey.2.2) := by
    rcases e1 with ⟨j, r, k⟩
    cases k <;> simp [GEdge.shift, GEdge.dstKey, GEdge.dstLayer, GEdge.dstLane, GEdge.dstPort] <;> omega
  have h2 : (e2.shift d).dstKey = (e2.dstKey.1 + d, e2.dstKey.2.1, e2.dstKey.2.2) := by
    rcases e2 with ⟨j, r, k⟩
    cases k <;> simp [GEdge.shift, GEdge.dstKey, GEdge.dstLayer, GEdge.dstLane, GEdge.dstPort] <;> omega
  rw [h1, h2, keyLt_shift]

private theorem srcKey_injective_of_odd {e1 e2 : GEdge}
    (h1 : e1.j % 2 = 1) (h2 : e2.j % 2 = 1) (heq : e1.srcKey = e2.srcKey) : e1 = e2 := by
  rcases e1 with ⟨j1, r1, k1⟩
  rcases e2 with ⟨j2, r2, k2⟩
  dsimp only at h1 h2
  cases k1 <;> cases k2 <;>
    simp only [GEdge.srcKey, GEdge.srcLayer, GEdge.srcLane, GEdge.srcPort, Prod.mk.injEq] at heq
  all_goals rcases heq with ⟨hjl, hrl, hpl⟩
  all_goals cases r1 <;> cases r2 <;> simp at hrl hpl
  all_goals try exact False.elim (by omega)
  all_goals exact congrArg (fun j => GEdge.mk j _ _) (by omega)

private theorem dstKey_injective_of_odd {e1 e2 : GEdge}
    (h1 : e1.j % 2 = 1) (h2 : e2.j % 2 = 1) (heq : e1.dstKey = e2.dstKey) : e1 = e2 := by
  rcases e1 with ⟨j1, r1, k1⟩
  rcases e2 with ⟨j2, r2, k2⟩
  dsimp only at h1 h2
  cases k1 <;> cases k2 <;>
    simp only [GEdge.dstKey, GEdge.dstLayer, GEdge.dstLane, GEdge.dstPort, Prod.mk.injEq] at heq
  all_goals rcases heq with ⟨hjl, hrl, hpl⟩
  all_goals cases r1 <;> cases r2 <;> simp at hrl hpl
  all_goals try exact False.elim (by omega)
  all_goals exact congrArg (fun j => GEdge.mk j _ _) (by omega)

theorem edgeDstLt_total_of_odd {e1 e2 : GEdge}
    (h1 : e1.j % 2 = 1) (h2 : e2.j % 2 = 1) (hne : e1 ≠ e2) :
    edgeDstLt e2 e1 = !edgeDstLt e1 e2 :=
  keyLt_total (fun heq => hne (dstKey_injective_of_odd h1 h2 heq))

theorem edgeDstLt_asym_of_odd {e1 e2 : GEdge}
    (h1 : e1.j % 2 = 1) (h2 : e2.j % 2 = 1) (hlt : edgeDstLt e1 e2 = true) :
    edgeDstLt e2 e1 = false := by
  by_cases he : e1 = e2
  · subst he; rw [edgeDstLt, keyLt_irrefl] at hlt; cases hlt
  · rw [edgeDstLt_total_of_odd h1 h2 he, hlt]; rfl

theorem edgeInvBit_symm_of_odd {e1 e2 : GEdge}
    (h1 : e1.j % 2 = 1) (h2 : e2.j % 2 = 1) :
    (edgeSrcLt e1 e2 != edgeDstLt e1 e2) = (edgeSrcLt e2 e1 != edgeDstLt e2 e1) := by
  by_cases he : e1 = e2
  · subst he; rfl
  · have hs : edgeSrcLt e2 e1 = !edgeSrcLt e1 e2 :=
      keyLt_total (fun heq => he (srcKey_injective_of_odd h1 h2 heq))
    have hd : edgeDstLt e2 e1 = !edgeDstLt e1 e2 :=
      keyLt_total (fun heq => he (dstKey_injective_of_odd h1 h2 heq))
    rw [hs, hd]
    cases edgeSrcLt e1 e2 <;> cases edgeDstLt e1 e2 <;> rfl

/-! ## 2. The 4-edge gadget `G^C_{j, r}` parity table -/

/-- The 4 edges of the two-lane gadget `G^C_{j, r}`: `[N_{j,r}, W_{j+1,!r}, E_{j+1,!r}, S_{j+2,r}]`. -/
def gadgetEdges (j : Int) (r : Bool) : List GEdge :=
  [⟨j, r, .N⟩, ⟨j, r, .W⟩, ⟨j, r, .E⟩, ⟨j, r, .S⟩]

private theorem gadgetEdges_shift (j : Int) (r : Bool) :
    gadgetEdges j r = (gadgetEdges 0 r).map (GEdge.shift j) := by
  simp [gadgetEdges, GEdge.shift]

private theorem pairInvSum_map_shift (d : Int) (xs : List GEdge) :
    pairInvSum edgeSrcLt edgeDstLt (fun _ => 1) (xs.map (GEdge.shift d)) =
      pairInvSum edgeSrcLt edgeDstLt (fun _ => 1) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, pairInvSum, List.map_map, ih]
    congr 1; congr 1
    apply List.map_congr_left
    intro y _; simp [edgeSrcLt_shift, edgeDstLt_shift]

private theorem crossInvSum_map_shift (d : Int) (xs ys : List GEdge) :
    crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (xs.map (GEdge.shift d)) (ys.map (GEdge.shift d)) =
      crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [crossInvSum, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [ih]; congr 1; congr 1
    apply List.map_congr_left
    intro y _; simp [edgeSrcLt_shift, edgeDstLt_shift]

/-- **L23 gadget self-inversion:** Every 4-edge gadget `G^C_{j, r}` has 3 (`≡ 1 mod 2`) self-inversions. -/
theorem gadget_self_inv_eq_three (j : Int) (r : Bool) :
    pairInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j r) = 3 := by
  rw [gadgetEdges_shift, pairInvSum_map_shift]
  cases r <;> decide

/-- **L23 gadget cross-inversion (`Δ = 0`, distinct lanes):** `G^C_{j, false}` and `G^C_{j, true}`
have 8 (`≡ 0 mod 2`) cross-inversions. -/
theorem gadget_cross_same_layer_eq_eight (j : Int) :
    crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j false) (gadgetEdges j true) = 8 := by
  rw [gadgetEdges_shift j false, gadgetEdges_shift j true, crossInvSum_map_shift]
  decide

/-- **L23 gadget cross-inversion (`Δ = 2`):** `G^C_{j, r1}` and `G^C_{j + 2, r2}` have odd
cross-inversion parity iff `r1 = r2` (exact counts: `1` for same lane, `0` or `2` for opposite lanes). -/
theorem gadget_cross_step_two_mod_two (j : Int) (r1 r2 : Bool) :
    crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j r1) (gadgetEdges (j + 2) r2) % 2 =
      if r1 = r2 then 1 else 0 := by
  have h2 : gadgetEdges (j + 2) r2 = (gadgetEdges 2 r2).map (GEdge.shift j) := by
    simp only [gadgetEdges, List.map_cons, List.map_nil, GEdge.shift]
    rw [show (2 : Int) + j = j + 2 by omega]
  rw [gadgetEdges_shift j r1, h2, crossInvSum_map_shift]
  cases r1 <;> cases r2 <;> decide

/-- **L23 gadget cross-inversion (`Δ ≥ 4`):** Gadgets separated by at least 4 layers have disjoint
layer intervals `[j1, j1+2] < [j2, j2+2]` in both source and target order, hence `0` cross-inversions. -/
theorem gadget_cross_ge_four_eq_zero {j1 j2 : Int} (h : j1 + 4 ≤ j2) (r1 r2 : Bool) :
    crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j1 r1) (gadgetEdges j2 r2) = 0 := by
  apply crossInvSum_eq_zero_of_all_false
  intro e1 he1 e2 he2
  have hs1 : e1.srcLayer ≤ j1 + 2 := by
    simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at he1
    rcases he1 with rfl | rfl | rfl | rfl <;> simp [GEdge.srcLayer] <;> omega
  have hd1 : e1.dstLayer ≤ j1 + 2 := by
    simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at he1
    rcases he1 with rfl | rfl | rfl | rfl <;> simp [GEdge.dstLayer] <;> omega
  have hs2 : j2 ≤ e2.srcLayer := by
    simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at he2
    rcases he2 with rfl | rfl | rfl | rfl <;> simp [GEdge.srcLayer] <;> omega
  have hd2 : j2 ≤ e2.dstLayer := by
    simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at he2
    rcases he2 with rfl | rfl | rfl | rfl <;> simp [GEdge.dstLayer] <;> omega
  have hslt : edgeSrcLt e1 e2 = true := by
    unfold edgeSrcLt GEdge.srcKey keyLt
    have : e1.srcLayer < e2.srcLayer := by omega
    simp [this]
  have hdlt : edgeDstLt e1 e2 = true := by
    unfold edgeDstLt GEdge.dstKey keyLt
    have : e1.dstLayer < e2.dstLayer := by omega
    simp [this]
  rw [hslt, hdlt]; rfl

/-- Gadget stack starting at odd layer `j0` for `m` steps of width `2`. -/
def gadgetStack (j0 : Int) : Nat → List GEdge
  | 0 => []
  | m + 1 => (gadgetEdges j0 false ++ gadgetEdges j0 true) ++ gadgetStack (j0 + 2) m

private theorem crossInvSum_gadget_stack_ge_four (j : Int) (r : Bool) (j0 : Int) (m : Nat)
    (h : j + 4 ≤ j0) :
    crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j r) (gadgetStack j0 m) = 0 := by
  induction m generalizing j0 with
  | zero => simp [gadgetStack, crossInvSum, gadgetEdges]
  | succ m ih =>
    simp only [gadgetStack, crossInvSum_append_right]
    rw [gadget_cross_ge_four_eq_zero h r false, gadget_cross_ge_four_eq_zero h r true,
      ih (j0 + 2) (by omega)]

private theorem gadget_wt_const (nBit : Int → Bool → Nat) (j : Int) (r : Bool) :
    ∀ e ∈ gadgetEdges j r, nBit e.j e.r = nBit j r := by
  intro e he
  simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> rfl

private theorem lane_sum_succ (nBit : Int → Bool → Nat) (j0 : Int) (m : Nat) (r : Bool) :
    ((List.range (m + 1)).map (fun k : Nat =>
      let j := j0 + 2 * (k : Int)
      nBit j r + nBit j r * nBit (j + 2) r)).sum =
    (nBit j0 r + nBit j0 r * nBit (j0 + 2) r) +
    ((List.range m).map (fun k : Nat =>
      let j := j0 + 2 + 2 * (k : Int)
      nBit j r + nBit j r * nBit (j + 2) r)).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  simp only [Int.natCast_zero, Int.mul_zero, Int.add_zero]
  congr 1; congr 1
  apply List.map_congr_left
  intro k _
  have heq : j0 + 2 * ((k + 1 : Nat) : Int) = j0 + 2 + 2 * (k : Int) := by omega
  simp only [Function.comp_def, heq]

/-- **L23 gadget-stack parity formula:** When every edge of `G^C_{j, r}` carries weight `nBit j r`
and `nBit` vanishes at `j0 + 2*m`, the total pair-inversion parity over `gadgetStack j0 m` equals
`∑_{r, k < m} (nBit (j0 + 2k) r + nBit (j0 + 2k) r * nBit (j0 + 2k + 2) r) (mod 2)`. -/
theorem gadgetStack_pairInvSum_mod_two (nBit : Int → Bool → Nat) (j0 : Int) (m : Nat)
    (hzero : nBit (j0 + 2 * (m : Int)) false = 0 ∧ nBit (j0 + 2 * (m : Int)) true = 0) :
    pairInvSum edgeSrcLt edgeDstLt (fun e => nBit e.j e.r) (gadgetStack j0 m) % 2 =
      (((List.range m).map (fun k : Nat =>
          let j := j0 + 2 * (k : Int)
          nBit j false + nBit j false * nBit (j + 2) false)).sum +
       ((List.range m).map (fun k : Nat =>
          let j := j0 + 2 * (k : Int)
          nBit j true + nBit j true * nBit (j + 2) true)).sum) % 2 := by
  induction m generalizing j0 with
  | zero => simp [gadgetStack, pairInvSum]
  | succ m ih =>
    have hzero' : nBit (j0 + 2 + 2 * (m : Int)) false = 0 ∧
        nBit (j0 + 2 + 2 * (m : Int)) true = 0 := by
      have heq : j0 + 2 + 2 * (m : Int) = j0 + 2 * ((m + 1 : Nat) : Int) := by omega
      rw [heq]; exact hzero
    have hih := ih (j0 + 2) hzero'
    have hselfF : pairInvSum edgeSrcLt edgeDstLt (fun e => nBit e.j e.r) (gadgetEdges j0 false) =
        3 * (nBit j0 false * nBit j0 false) := by
      rw [pairInvSum_const_wt _ _ _ _ _ (gadget_wt_const nBit j0 false), gadget_self_inv_eq_three]
    have hselfT : pairInvSum edgeSrcLt edgeDstLt (fun e => nBit e.j e.r) (gadgetEdges j0 true) =
        3 * (nBit j0 true * nBit j0 true) := by
      rw [pairInvSum_const_wt _ _ _ _ _ (gadget_wt_const nBit j0 true), gadget_self_inv_eq_three]
    have hcross0 : crossInvSum edgeSrcLt edgeDstLt (fun e => nBit e.j e.r)
        (gadgetEdges j0 false) (gadgetEdges j0 true) =
        8 * (nBit j0 false * nBit j0 true) := by
      rw [crossInvSum_const_wt _ _ _ _ _ _ _ (gadget_wt_const nBit j0 false)
        (gadget_wt_const nBit j0 true), gadget_cross_same_layer_eq_eight]
    have hcrossRest :
        crossInvSum edgeSrcLt edgeDstLt (fun e => nBit e.j e.r)
          (gadgetEdges j0 false ++ gadgetEdges j0 true) (gadgetStack (j0 + 2) m) % 2 =
        (nBit j0 false * nBit (j0 + 2) false + nBit j0 true * nBit (j0 + 2) true) % 2 := by
      cases m with
      | zero =>
        simp only [Int.natCast_zero, Int.mul_zero, Int.add_zero] at hzero'
        simp [gadgetStack, crossInvSum, gadgetEdges, hzero'.1, hzero'.2]
      | succ m' =>
        simp only [gadgetStack, crossInvSum_append_left, crossInvSum_append_right]
        have hzero_ge : ∀ r : Bool,
            crossInvSum edgeSrcLt edgeDstLt (fun e => nBit e.j e.r)
              (gadgetEdges j0 r) (gadgetStack (j0 + 2 + 2) m') = 0 := fun r =>
          crossInvSum_eq_zero_of_unit_eq_zero _ _ _ _ _
            (crossInvSum_gadget_stack_ge_four j0 r (j0 + 2 + 2) m' (by omega))
        rw [hzero_ge false, hzero_ge true]
        have hc : ∀ r1 r2 : Bool,
            crossInvSum edgeSrcLt edgeDstLt (fun e => nBit e.j e.r)
              (gadgetEdges j0 r1) (gadgetEdges (j0 + 2) r2) =
            crossInvSum edgeSrcLt edgeDstLt (fun _ => 1)
              (gadgetEdges j0 r1) (gadgetEdges (j0 + 2) r2) *
              (nBit j0 r1 * nBit (j0 + 2) r2) := fun r1 r2 =>
          crossInvSum_const_wt _ _ _ _ _ _ _ (gadget_wt_const nBit j0 r1)
            (gadget_wt_const nBit (j0 + 2) r2)
        rw [hc false false, hc false true, hc true false, hc true true]
        have hFF := gadget_cross_step_two_mod_two j0 false false
        have hFT := gadget_cross_step_two_mod_two j0 false true
        have hTF := gadget_cross_step_two_mod_two j0 true false
        have hTT := gadget_cross_step_two_mod_two j0 true true
        simp only [ite_true, Bool.false_eq_true, ite_false, Bool.true_eq_false] at hFF hFT hTF hTT
        have mFF : (crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j0 false) (gadgetEdges (j0 + 2) false) *
            (nBit j0 false * nBit (j0 + 2) false)) % 2 = (nBit j0 false * nBit (j0 + 2) false) % 2 := by
          rw [Nat.mul_mod, hFF, Nat.one_mul, Nat.mod_mod]
        have mFT : (crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j0 false) (gadgetEdges (j0 + 2) true) *
            (nBit j0 false * nBit (j0 + 2) true)) % 2 = 0 := by
          rw [Nat.mul_mod, hFT, Nat.zero_mul]
        have mTF : (crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j0 true) (gadgetEdges (j0 + 2) false) *
            (nBit j0 true * nBit (j0 + 2) false)) % 2 = 0 := by
          rw [Nat.mul_mod, hTF, Nat.zero_mul]
        have mTT : (crossInvSum edgeSrcLt edgeDstLt (fun _ => 1) (gadgetEdges j0 true) (gadgetEdges (j0 + 2) true) *
            (nBit j0 true * nBit (j0 + 2) true)) % 2 = (nBit j0 true * nBit (j0 + 2) true) % 2 := by
          rw [Nat.mul_mod, hTT, Nat.one_mul, Nat.mod_mod]
        omega
    have hsq : ∀ a : Nat, (a * a) % 2 = a % 2 := by
      intro a
      have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases ha with h | h <;> rw [Nat.mul_mod, h] <;> decide
    simp only [gadgetStack, pairInvSum_append, hselfF, hselfT, hcross0]
    rw [lane_sum_succ nBit j0 m false, lane_sum_succ nBit j0 m true]
    have hsqF := hsq (nBit j0 false)
    have hsqT := hsq (nBit j0 true)
    omega

/-! ## 3. Window vertices, lexicographic edge orders, and permutation to `gadgetStack` -/

/-- All layers `j0, j0 + 1, …, j0 + 2*m` in increasing order. -/
def windowLayers (j0 : Int) (m : Nat) : List Int :=
  (List.range (2 * m + 1)).map (fun k : Nat => j0 + (k : Int))

/-- All `(layer, lane)` vertices in `[j0, j0 + 2*m]` in lexicographic `(t, r)` order. -/
def windowVertices (j0 : Int) (m : Nat) : List (Int × Bool) :=
  (windowLayers j0 m).flatMap (fun t => [(t, false), (t, true)])

/-- Internal outgoing quotient edges from vertex `v = (t, r)` in `[j0, j0 + 2*m]`, ordered by
`srcPort` (`false` before `true`). -/
def windowOutEdges (j0 : Int) (m : Nat) (v : Int × Bool) : List GEdge :=
  let t := v.1
  let r := v.2
  if t % 2 = 0 then
    [⟨t - 1, !r, .W⟩, ⟨t - 1, !r, .E⟩]
  else
    (if j0 < t then [⟨t - 2, r, .S⟩] else []) ++
      (if t < j0 + 2 * (m : Int) then [⟨t, r, .N⟩] else [])

/-- Internal incoming quotient edges to vertex `v = (t, r)` in `[j0, j0 + 2*m]`, ordered by
`dstPort` (`false` before `true`). -/
def windowInEdges (j0 : Int) (m : Nat) (v : Int × Bool) : List GEdge :=
  let t := v.1
  let r := v.2
  if t % 2 = 0 then
    [⟨t - 1, r, .S⟩, ⟨t - 1, r, .N⟩]
  else
    (if t < j0 + 2 * (m : Int) then [⟨t, r, .W⟩] else []) ++
      (if j0 < t then [⟨t - 2, r, .E⟩] else [])

def windowSrcOrder (j0 : Int) (m : Nat) : List GEdge :=
  (windowVertices j0 m).flatMap (windowOutEdges j0 m)

def windowDstOrder (j0 : Int) (m : Nat) : List GEdge :=
  (windowVertices j0 m).flatMap (windowInEdges j0 m)

private def vtxLt (a b : Int × Bool) : Bool :=
  if a.1 < b.1 then true
  else if b.1 < a.1 then false
  else (!a.2) && b.2

private theorem pairwise_flatMap_of_key {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    {xs : List α} {f : α → List β}
    (hxs : xs.Pairwise R)
    (hf_in : ∀ a ∈ xs, (f a).Pairwise S)
    (hf_cross : ∀ a ∈ xs, ∀ b ∈ xs, R a b → ∀ x ∈ f a, ∀ y ∈ f b, S x y) :
    (xs.flatMap f).Pairwise S := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha_lt, hxs'⟩ := List.pairwise_cons.mp hxs
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨hf_in a (by simp),
      ih hxs' (fun b hb => hf_in b (by simp [hb]))
        (fun b1 hb1 b2 hb2 => hf_cross b1 (by simp [hb1]) b2 (by simp [hb2])), ?_⟩
    intro x hx y hy
    obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
    exact hf_cross a (by simp) b (by simp [hb]) (ha_lt b hb) x hx y hyb

private theorem nodup_of_pairwise_irrefl {α : Type} {R : α → α → Prop} {xs : List α}
    (hpw : xs.Pairwise R) (hirr : ∀ a, ¬ R a a) : xs.Nodup :=
  hpw.imp (fun {a b} (h : R a b) (heq : a = b) => hirr a (heq ▸ h))

theorem mem_windowLayers {j0 t : Int} {m : Nat} :
    t ∈ windowLayers j0 m ↔ j0 ≤ t ∧ t ≤ j0 + 2 * (m : Int) := by
  unfold windowLayers
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' := List.mem_range.mp hk
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(t - j0).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

theorem mem_windowVertices {j0 t : Int} {r : Bool} {m : Nat} :
    (t, r) ∈ windowVertices j0 m ↔ j0 ≤ t ∧ t ≤ j0 + 2 * (m : Int) := by
  unfold windowVertices
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨t', ht', hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact mem_windowLayers.mp ht'
  · intro h
    refine ⟨t, mem_windowLayers.mpr h, ?_⟩
    cases r <;> simp

private theorem windowVertices_pairwise (j0 : Int) (m : Nat) :
    (windowVertices j0 m).Pairwise (fun a b => vtxLt a b = true) := by
  have hlayers : (windowLayers j0 m).Pairwise (fun t1 t2 => t1 < t2) := by
    unfold windowLayers
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun {a b} hab => by omega)
  apply pairwise_flatMap_of_key hlayers
  · intro t _
    exact List.Pairwise.cons (fun b hb => by
      simp only [List.mem_singleton] at hb; subst hb; simp [vtxLt])
      (List.Pairwise.cons (by simp) List.Pairwise.nil)
  · intro t1 _ t2 _ hlt x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [vtxLt, hlt]

theorem windowVertices_nodup (j0 : Int) (m : Nat) : (windowVertices j0 m).Nodup :=
  nodup_of_pairwise_irrefl (windowVertices_pairwise j0 m) (by
    intro ⟨t, r⟩ h; cases r <;> simp [vtxLt] at h)

private theorem windowOutEdges_src {j0 : Int} {m : Nat} {v : Int × Bool} {e : GEdge}
    (he : e ∈ windowOutEdges j0 m v) : e.srcLayer = v.1 ∧ e.srcLane = v.2 := by
  rcases v with ⟨t, r⟩
  unfold windowOutEdges at he
  by_cases ht : t % 2 = 0
  · simp only [ht, ite_true, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [GEdge.srcLayer, GEdge.srcLane] <;> omega
  · simp only [ht, ite_false, List.mem_append] at he
    rcases he with h1 | h2
    · split at h1 <;> simp at h1; subst h1; simp [GEdge.srcLayer, GEdge.srcLane]
    · split at h2 <;> simp at h2; subst h2; simp [GEdge.srcLayer, GEdge.srcLane]

private theorem windowInEdges_dst {j0 : Int} {m : Nat} {v : Int × Bool} {e : GEdge}
    (he : e ∈ windowInEdges j0 m v) : e.dstLayer = v.1 ∧ e.dstLane = v.2 := by
  rcases v with ⟨t, r⟩
  unfold windowInEdges at he
  by_cases ht : t % 2 = 0
  · simp only [ht, ite_true, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [GEdge.dstLayer, GEdge.dstLane]
  · simp only [ht, ite_false, List.mem_append] at he
    rcases he with h1 | h2
    · split at h1 <;> simp at h1; subst h1; simp [GEdge.dstLayer, GEdge.dstLane]
    · split at h2 <;> simp at h2; subst h2; simp [GEdge.dstLayer, GEdge.dstLane]

theorem windowSrcOrder_pairwise (j0 : Int) (m : Nat) :
    (windowSrcOrder j0 m).Pairwise (fun a b => edgeSrcLt a b = true) := by
  apply pairwise_flatMap_of_key (windowVertices_pairwise j0 m)
  · intro ⟨t, r⟩ _
    unfold windowOutEdges
    by_cases ht : t % 2 = 0
    · simp only [ht, ite_true]
      exact List.Pairwise.cons (fun b hb => by
        simp only [List.mem_singleton] at hb; subst hb
        unfold edgeSrcLt GEdge.srcKey GEdge.srcLayer GEdge.srcLane GEdge.srcPort keyLt
        simp) (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · simp only [ht, ite_false]
      split <;> split <;> simp [edgeSrcLt, GEdge.srcKey, GEdge.srcLayer, GEdge.srcLane,
        GEdge.srcPort, keyLt]
  · intro a _ b _ hlt x hx y hy
    obtain ⟨hx1, hx2⟩ := windowOutEdges_src hx
    obtain ⟨hy1, hy2⟩ := windowOutEdges_src hy
    unfold edgeSrcLt GEdge.srcKey keyLt
    rw [hx1, hx2, hy1, hy2]
    rcases a with ⟨t1, r1⟩; rcases b with ⟨t2, r2⟩
    unfold vtxLt at hlt
    by_cases h1 : t1 < t2
    · simp [h1]
    · by_cases h2 : t2 < t1
      · simp [h1, h2] at hlt
      · simp only [h1, h2, ite_false] at hlt ⊢
        cases r1 <;> cases r2 <;> simp at hlt ⊢

theorem windowDstOrder_pairwise (j0 : Int) (m : Nat) :
    (windowDstOrder j0 m).Pairwise (fun a b => edgeDstLt a b = true) := by
  apply pairwise_flatMap_of_key (windowVertices_pairwise j0 m)
  · intro ⟨t, r⟩ _
    unfold windowInEdges
    by_cases ht : t % 2 = 0
    · simp only [ht, ite_true]
      exact List.Pairwise.cons (fun b hb => by
        simp only [List.mem_singleton] at hb; subst hb
        unfold edgeDstLt GEdge.dstKey GEdge.dstLayer GEdge.dstLane GEdge.dstPort keyLt
        simp) (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · simp only [ht, ite_false]
      split <;> split <;> simp [edgeDstLt, GEdge.dstKey, GEdge.dstLayer, GEdge.dstLane,
        GEdge.dstPort, keyLt]
  · intro a _ b _ hlt x hx y hy
    obtain ⟨hx1, hx2⟩ := windowInEdges_dst hx
    obtain ⟨hy1, hy2⟩ := windowInEdges_dst hy
    unfold edgeDstLt GEdge.dstKey keyLt
    rw [hx1, hx2, hy1, hy2]
    rcases a with ⟨t1, r1⟩; rcases b with ⟨t2, r2⟩
    unfold vtxLt at hlt
    by_cases h1 : t1 < t2
    · simp [h1]
    · by_cases h2 : t2 < t1
      · simp [h1, h2] at hlt
      · simp only [h1, h2, ite_false] at hlt ⊢
        cases r1 <;> cases r2 <;> simp at hlt ⊢

theorem windowSrcOrder_nodup (j0 : Int) (m : Nat) : (windowSrcOrder j0 m).Nodup :=
  nodup_of_pairwise_irrefl (windowSrcOrder_pairwise j0 m) (by
    intro e h; rw [edgeSrcLt, keyLt_irrefl] at h; cases h)

theorem windowDstOrder_nodup (j0 : Int) (m : Nat) : (windowDstOrder j0 m).Nodup :=
  nodup_of_pairwise_irrefl (windowDstOrder_pairwise j0 m) (by
    intro e h; rw [edgeDstLt, keyLt_irrefl] at h; cases h)

theorem mem_gadgetStack_iff {j0 : Int} (hj0 : j0 % 2 = 1) {m : Nat} {e : GEdge} :
    e ∈ gadgetStack j0 m ↔ e.j % 2 = 1 ∧ j0 ≤ e.j ∧ e.j < j0 + 2 * (m : Int) := by
  induction m generalizing j0 with
  | zero =>
    simp only [gadgetStack, List.not_mem_nil, Int.natCast_zero, Int.mul_zero, Int.add_zero,
      false_iff]
    omega
  | succ m ih =>
    simp only [gadgetStack, List.mem_append, ih (show (j0 + 2) % 2 = 1 by omega)]
    have hge : e ∈ gadgetEdges j0 false ∨ e ∈ gadgetEdges j0 true ↔ e.j = j0 := by
      rcases e with ⟨j, r, k⟩
      constructor
      · intro h
        rcases h with h | h <;>
          simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false, GEdge.mk.injEq] at h <;>
          rcases h with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> rfl
      · rintro rfl
        cases r <;> cases k <;> simp [gadgetEdges]
    rw [hge]
    constructor
    · rintro (rfl | ⟨ho, hlo, hhi⟩) <;> omega
    · rintro ⟨ho, hlo, hhi⟩
      by_cases h0 : e.j = j0
      · exact Or.inl h0
      · exact Or.inr ⟨ho, by omega, by omega⟩

theorem gadgetStack_nodup (j0 : Int) (m : Nat) : (gadgetStack j0 m).Nodup := by
  induction m generalizing j0 with
  | zero => simp [gadgetStack]
  | succ m ih =>
    simp only [gadgetStack, List.nodup_append]
    refine ⟨?_, ih (j0 + 2), ?_⟩
    · refine ⟨by simp [gadgetEdges], by simp [gadgetEdges], ?_⟩
      intro a ha b hb heq; subst heq
      simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with hb | hb | hb | hb <;> cases hb
    · intro a ha b hb heq; subst heq
      have haj : a.j = j0 := by
        rcases List.mem_append.mp ha with h | h <;>
          simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at h <;>
          rcases h with rfl | rfl | rfl | rfl <;> rfl
      have hbj : j0 + 2 ≤ a.j := by
        have hlo : ∀ (j1 : Int) (n : Nat) (x : GEdge), x ∈ gadgetStack j1 n → j1 ≤ x.j := by
          intro j1 n
          induction n generalizing j1 with
          | zero => intro x hx; simp [gadgetStack] at hx
          | succ n ihn =>
            intro x hx
            simp only [gadgetStack, List.mem_append] at hx
            rcases hx with (h | h) | h
            · simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl | rfl | rfl <;> dsimp only <;> omega
            · simp only [gadgetEdges, List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl | rfl | rfl <;> dsimp only <;> omega
            · have := ihn (j1 + 2) x h; omega
        exact hlo (j0 + 2) m a hb
      omega

theorem mem_windowSrcOrder_iff {j0 : Int} (hj0 : j0 % 2 = 1) {m : Nat} {e : GEdge} :
    e ∈ windowSrcOrder j0 m ↔ e ∈ gadgetStack j0 m := by
  rw [mem_gadgetStack_iff hj0]
  unfold windowSrcOrder
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨t, r⟩, hv, he⟩
    obtain ⟨hlo, hhi⟩ := mem_windowVertices.mp hv
    unfold windowOutEdges at he
    by_cases ht : t % 2 = 0
    · simp only [ht, ite_true, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> dsimp only <;> refine ⟨by omega, by omega, by omega⟩
    · simp only [ht, ite_false, List.mem_append] at he
      rcases he with h1 | h2
      · split at h1 <;> simp at h1; subst h1; dsimp only; omega
      · split at h2 <;> simp at h2; subst h2; dsimp only; omega
  · rintro ⟨hodd, hlo, hhi⟩
    rcases e with ⟨j, r, k⟩
    dsimp only at hodd hlo hhi
    refine ⟨(GEdge.srcLayer ⟨j, r, k⟩, GEdge.srcLane ⟨j, r, k⟩), mem_windowVertices.mpr ?_, ?_⟩
    · cases k <;> simp [GEdge.srcLayer] <;> omega
    · cases k <;> unfold windowOutEdges <;> simp only [GEdge.srcLayer, GEdge.srcLane]
      · have hne : j % 2 ≠ 0 := by omega
        have hlt : j < j0 + 2 * (m : Int) := by omega
        simp [hne, hlt]
      · have hev : (j + 1) % 2 = 0 := by omega
        simp [hev]
      · have hev : (j + 1) % 2 = 0 := by omega
        simp [hev]
      · have hne' : j % 2 ≠ 0 := by omega
        have hgt : j0 < j + 2 := by omega
        simp [hne', hgt]

theorem mem_windowDstOrder_iff {j0 : Int} (hj0 : j0 % 2 = 1) {m : Nat} {e : GEdge} :
    e ∈ windowDstOrder j0 m ↔ e ∈ gadgetStack j0 m := by
  rw [mem_gadgetStack_iff hj0]
  unfold windowDstOrder
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨t, r⟩, hv, he⟩
    obtain ⟨hlo, hhi⟩ := mem_windowVertices.mp hv
    unfold windowInEdges at he
    by_cases ht : t % 2 = 0
    · simp only [ht, ite_true, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> dsimp only <;> refine ⟨by omega, by omega, by omega⟩
    · simp only [ht, ite_false, List.mem_append] at he
      rcases he with h1 | h2
      · split at h1 <;> simp at h1; subst h1; dsimp only; omega
      · split at h2 <;> simp at h2; subst h2; dsimp only; omega
  · rintro ⟨hodd, hlo, hhi⟩
    rcases e with ⟨j, r, k⟩
    dsimp only at hodd hlo hhi
    refine ⟨(GEdge.dstLayer ⟨j, r, k⟩, GEdge.dstLane ⟨j, r, k⟩), mem_windowVertices.mpr ?_, ?_⟩
    · cases k <;> simp [GEdge.dstLayer] <;> omega
    · cases k <;> unfold windowInEdges <;> simp only [GEdge.dstLayer, GEdge.dstLane]
      · have hev : (j + 1) % 2 = 0 := by omega
        simp [hev]
      · have hne : j % 2 ≠ 0 := by omega
        have hlt : j < j0 + 2 * (m : Int) := by omega
        simp [hne, hlt]
      · have hne' : j % 2 ≠ 0 := by omega
        have hgt : j0 < j + 2 := by omega
        simp [hne', hgt]
      · have hev : (j + 1) % 2 = 0 := by omega
        simp [hev]

theorem windowSrcOrder_perm_gadgetStack {j0 : Int} (hj0 : j0 % 2 = 1) (m : Nat) :
    (windowSrcOrder j0 m).Perm (gadgetStack j0 m) :=
  (List.perm_ext_iff_of_nodup (windowSrcOrder_nodup j0 m) (gadgetStack_nodup j0 m)).mpr
    (fun _ => mem_windowSrcOrder_iff hj0)

theorem windowDstOrder_perm_gadgetStack {j0 : Int} (hj0 : j0 % 2 = 1) (m : Nat) :
    (windowDstOrder j0 m).Perm (gadgetStack j0 m) :=
  (List.perm_ext_iff_of_nodup (windowDstOrder_nodup j0 m) (gadgetStack_nodup j0 m)).mpr
    (fun _ => mem_windowDstOrder_iff hj0)

theorem windowSrcOrder_perm_windowDstOrder {j0 : Int} (hj0 : j0 % 2 = 1) (m : Nat) :
    (windowSrcOrder j0 m).Perm (windowDstOrder j0 m) :=
  (windowSrcOrder_perm_gadgetStack hj0 m).trans (windowDstOrder_perm_gadgetStack hj0 m).symm

end TwoCellDiagonal
end LangtonsAnt
