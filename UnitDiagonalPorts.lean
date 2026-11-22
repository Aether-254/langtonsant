import LangtonsAnt

/-!
# Diagonal ports

Part A: closed walks from an arbitrary grid point with no intermediate return to
the start point (the diagonal "ports" of the two diagonal translations).

Part B: purely combinatorial counting identities for the parity-flipped port word.
No subtraction on naturals is used.  Both identities were brute-force checked during
development for every Boolean list of length at most 11; the checks were deleted and
the theorems below are proved unconditionally.

Every declaration below is checked by the Lean kernel: no `sorry`, no `axiom`,
no `native_decide`.
-/

namespace UnitDiagonal

open LangtonsAnt

/-! ## Part A: geometric certificates -/

/-- Position reached after following a list of move directions from `p`. -/
def walk (p : Point) : List Direction → Point
  | [] => p
  | d :: ds => walk (move p d) ds

/-- Every position visited while following `ds` from `p`, including start and end. -/
def walkPts (p : Point) : List Direction → List Point
  | [] => [p]
  | d :: ds => p :: walkPts (move p d) ds

theorem walkPts_head (p : Point) (ds : List Direction) : (walkPts p ds).head? = some p := by
  cases ds <;> rfl

theorem walkPts_length (p : Point) (ds : List Direction) :
    (walkPts p ds).length = ds.length + 1 := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [walkPts, ih]

/-- The positions strictly between start and end: after `k` steps with `0 < k < ds.length`. -/
def interiorPts (p : Point) (ds : List Direction) : List Point :=
  (List.range ds.length).filterMap fun k =>
    if k = 0 then none else some (walk p (ds.take k))

/-- `ds` returns to `p` and no intermediate position equals `p`. -/
def FirstReturn (p : Point) (ds : List Direction) : Prop :=
  walk p ds = p ∧ p ∉ interiorPts p ds

theorem mem_interiorPts {p : Point} {ds : List Direction} {k : Nat}
    (h0 : 0 < k) (hk : k < ds.length) : walk p (ds.take k) ∈ interiorPts p ds := by
  simp only [interiorPts, List.mem_filterMap, List.mem_range]
  refine ⟨k, hk, ?_⟩
  have hk0 : ¬ (k = 0) := by omega
  simp [hk0]

theorem exists_of_mem_interiorPts {p q : Point} {ds : List Direction}
    (h : q ∈ interiorPts p ds) :
    ∃ k, 0 < k ∧ k < ds.length ∧ q = walk p (ds.take k) := by
  simp only [interiorPts, List.mem_filterMap, List.mem_range] at h
  obtain ⟨k, hk, hkq⟩ := h
  by_cases hk0 : k = 0
  · simp [hk0] at hkq
  · exact ⟨k, Nat.pos_of_ne_zero hk0, hk, by simpa [hk0] using hkq.symm⟩

/-- The faithful restatement: `ds` returns to `p`, and no `k` with `0 < k < ds.length`
leads back to `p`. -/
theorem firstReturn_iff (p : Point) (ds : List Direction) :
    FirstReturn p ds ↔
      walk p ds = p ∧ ∀ k, 0 < k → k < ds.length → walk p (ds.take k) ≠ p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hwalk, hmem⟩
    refine ⟨hwalk, ?_⟩
    intro k h0 hk heq
    have hmem' : walk p (ds.take k) ∈ interiorPts p ds := mem_interiorPts h0 hk
    rw [heq] at hmem'
    exact hmem hmem'
  · rintro ⟨hwalk, hne⟩
    refine ⟨hwalk, ?_⟩
    intro hmem
    obtain ⟨k, h0, hk, hq⟩ := exists_of_mem_interiorPts hmem
    exact hne k h0 hk hq.symm

/-! ### The two-step diagonal port -/

theorem walk_east_south (p : Point) :
    walk p [.east, .south] = (p.1 + 1, p.2 - 1) := by
  obtain ⟨x, y⟩ := p
  simp [walk, move]

/-! ### Closed walks with no intermediate return -/

theorem firstReturn_NESW (p : Point) :
    FirstReturn p [.north, .east, .south, .west] := by
  rw [firstReturn_iff]
  obtain ⟨x, y⟩ := p
  refine ⟨by simp [walk, move], ?_⟩
  intro k h0 hk
  have hk4 : k < 4 := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl <;>
    simp [walk, move, Prod.ext_iff] <;> omega

theorem firstReturn_ENWS (p : Point) :
    FirstReturn p [.east, .north, .west, .south] := by
  rw [firstReturn_iff]
  obtain ⟨x, y⟩ := p
  refine ⟨by simp [walk, move], ?_⟩
  intro k h0 hk
  have hk4 : k < 4 := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl <;>
    simp [walk, move, Prod.ext_iff] <;> omega

theorem firstReturn_SENW (p : Point) :
    FirstReturn p [.south, .east, .north, .west] := by
  rw [firstReturn_iff]
  obtain ⟨x, y⟩ := p
  refine ⟨by simp [walk, move], ?_⟩
  intro k h0 hk
  have hk4 : k < 4 := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl <;>
    simp [walk, move, Prod.ext_iff] <;> omega

theorem firstReturn_NWSE (p : Point) :
    FirstReturn p [.north, .west, .south, .east] := by
  rw [firstReturn_iff]
  obtain ⟨x, y⟩ := p
  refine ⟨by simp [walk, move], ?_⟩
  intro k h0 hk
  have hk4 : k < 4 := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl <;>
    simp [walk, move, Prod.ext_iff] <;> omega

theorem firstReturn_ENESWNWS (p : Point) :
    FirstReturn p [.east, .north, .east, .south, .west, .north, .west, .south] := by
  rw [firstReturn_iff]
  obtain ⟨x, y⟩ := p
  refine ⟨by simp [walk, move], ?_⟩
  intro k h0 hk
  have hk8 : k < 8 := hk
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [walk, move, Prod.ext_iff] <;> omega

/-! ## Part B: abstract port counting (independent of the ant) -/

/-- Number of `true` entries of a Boolean list. -/
def countTrue : List Bool → Nat
  | [] => 0
  | b :: l => (if b then 1 else 0) + countTrue l

/-- Number of `true` entries at even indices `0, 2, 4, ...`. -/
def evenTrue : List Bool → Nat
  | [] => 0
  | [a] => (if a then 1 else 0)
  | a :: _ :: rest => (if a then 1 else 0) + evenTrue rest

/-- The next-layer port word: `beta[k] = alpha[k] XOR (k odd) XOR t`,
where `t` is the parity of the layer (`t = true` for an odd layer). -/
def beta : List Bool → Bool → List Bool
  | [], _ => []
  | a :: α, t => (a != t) :: beta α (!t)

theorem beta_length (α : List Bool) (t : Bool) : (beta α t).length = α.length := by
  induction α generalizing t with
  | nil => rfl
  | cons a α ih => simp [beta, ih]

/-- Flipping the layer parity complements the port word pointwise. -/
theorem beta_true_eq_map_not (α : List Bool) :
    beta α true = (beta α false).map (!·) := by
  induction α with
  | nil => rfl
  | cons a α ih => simp [beta, ih, List.map_map, Function.comp_def]

theorem decide_mod_two_succ (k : Nat) :
    decide ((k + 1) % 2 = 1) = !decide (k % 2 = 1) := by
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with h | h
  · have h1 : (k + 1) % 2 = 1 := by omega
    simp [h, h1]
  · have h1 : (k + 1) % 2 = 0 := by omega
    simp [h, h1]

/-- Pointwise specification: `beta[k] = alpha[k] XOR (k odd) XOR t`. -/
theorem beta_spec (α : List Bool) (t : Bool) (k : Nat) :
    (beta α t)[k]? = (α[k]?).map (fun a => (a != decide (k % 2 = 1)) != t) := by
  induction α generalizing k t with
  | nil => rfl
  | cons a α ih =>
    cases k with
    | zero => cases a <;> cases t <;> rfl
    | succ j =>
      simp only [beta, List.getElem?_cons_succ, decide_mod_two_succ, ih]
      cases α[j]? with
      | none => rfl
      | some b => cases b <;> cases t <;> cases decide (j % 2 = 1) <;> rfl

theorem countTrue_add_countTrue_beta (α : List Bool) :
    countTrue (beta α false) + countTrue (beta α true) = α.length := by
  induction α with
  | nil => rfl
  | cons a α ih =>
    cases a <;> simp [beta, countTrue] <;> omega

/-! ### The two counting identities -/

/-- Even layer (`t = false`): `n + 4e = 2I + 2J + o`. -/
theorem even_layer (α : List Bool) :
    α.length + 4 * evenTrue α =
      2 * countTrue α + 2 * countTrue (beta α false) + α.length % 2 := by
  induction α using evenTrue.induct with
  | case1 => rfl
  | case2 => simp [evenTrue, countTrue, beta]
  | case3 a ha =>
    cases a
    · simp [evenTrue, countTrue, beta]
    · exact absurd rfl ha
  | case4 a b rest ih =>
    cases a <;> cases b <;> simp [evenTrue, countTrue, beta] at ih ⊢ <;> omega

/-- Odd layer (`t = true`): `n + 2I + o = 2J + 4e`. -/
theorem odd_layer (α : List Bool) :
    α.length + 2 * countTrue α + α.length % 2 =
      2 * countTrue (beta α true) + 4 * evenTrue α := by
  induction α using evenTrue.induct with
  | case1 => rfl
  | case2 => simp [evenTrue, countTrue, beta]
  | case3 a ha =>
    cases a
    · simp [evenTrue, countTrue, beta]
    · exact absurd rfl ha
  | case4 a b rest ih =>
    cases a <;> cases b <;> simp [evenTrue, countTrue, beta] at ih ⊢ <;> omega


end UnitDiagonal
