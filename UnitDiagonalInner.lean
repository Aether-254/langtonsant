import UnitDiagonalCore

/-!
# Third-inner-layer forcing and exclusion of `(1, -1)` drift

Completes L23–L29 of the unit-diagonal exclusion blueprint on top of `UnitDiagonalCore`:

* **L23**: Fixed actual successor paths above layer `B = topLayer - 2`
  (`B₁ → A₁ → B₅` and `B₃ → A₂ → T → A₀ → B₄ → A₃ → B₇`) together with `B`'s
  downward-departure and from-below-arrival rank lists.
* **L24**: Layer `C = topLayer - 3` (odd depth) has upper arrival/departure rank lists
  `p`, `q` of length `≥ 5` whose first five entries match `B`'s downward departures
  `[0, 2, 5, 6, 7]` and from-below arrivals `[0, 1, 2, 3, 6]`.
* **L25**: First returns `ENWS` and `ENESWNWS` force `p[2] = q[1] + 1` and
  `p[4] = q[3] + 1`.
* **L26–L27**: First returns `SENW` and `NWSE` forbid `p[1] = q[1]` and `p[4] = q[4]`.
* **L29**: Applying `interleave_bridge` on layer `C` yields `False`.

All proofs are pure Lean kernel proofs (no `sorry`, no `axiom`, no `native_decide`).
-/
namespace UnitDiagonal
open LangtonsAnt

/-! ## Helpers: eight-step first return and directed port stepping -/

private theorem path_succ {P len : Nat} (p : ContinuousPhasePath P len)
    {r : Nat} (hr : r < len) :
    p.phase (r + 1) = UnitDiagonalMatching.succ P (p.phase r) := by
  rcases p.successor hr with ⟨hs, _⟩ | ⟨he, hz, _⟩
  · rw [UnitDiagonalMatching.succ, ← hs, Nat.mod_eq_of_lt (p.phase_lt _ (by omega))]
  · simp [UnitDiagonalMatching.succ, he, hz]

/-- An eight-edge physical first return advances rank by one. Every edge is supplied
as an actual cyclic successor; there is no assumption that the period exceeds eight. -/
theorem eight_step_return_rank
    {P i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ : Nat} {w : Nat → Bool}
    (hd : wordDrift P w = (1, -1)) (hi : i₀ < P)
    (hs₀ : UnitDiagonalMatching.succ P i₀ = i₁)
    (hs₁ : UnitDiagonalMatching.succ P i₁ = i₂)
    (hs₂ : UnitDiagonalMatching.succ P i₂ = i₃)
    (hs₃ : UnitDiagonalMatching.succ P i₃ = i₄)
    (hs₄ : UnitDiagonalMatching.succ P i₄ = i₅)
    (hs₅ : UnitDiagonalMatching.succ P i₅ = i₆)
    (hs₆ : UnitDiagonalMatching.succ P i₆ = i₇)
    (hs₇ : UnitDiagonalMatching.succ P i₇ = i₈)
    (d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ : Direction)
    (hd₀ : outDir w i₀ = d₀) (hd₁ : outDir w i₁ = d₁)
    (hd₂ : outDir w i₂ = d₂) (hd₃ : outDir w i₃ = d₃)
    (hd₄ : outDir w i₄ = d₄) (hd₅ : outDir w i₅ = d₅)
    (hd₆ : outDir w i₆ = d₆) (hd₇ : outDir w i₇ = d₇)
    (hret : ∀ q, FirstReturn q [d₀, d₁, d₂, d₃, d₄, d₅, d₆, d₇]) :
    stableRank P w i₈ = stableRank P w i₀ + 1 := by
  let p := ContinuousPhasePath.ofStart (show 0 < P by omega) i₀ 8
  have hp₀ : p.phase 0 = i₀ := by simp [p, ContinuousPhasePath.ofStart, Nat.mod_eq_of_lt hi]
  have hp₁ : p.phase 1 = i₁ := by rw [path_succ p (by decide : 0 < 8), hp₀, hs₀]
  have hp₂ : p.phase 2 = i₂ := by rw [path_succ p (by decide : 1 < 8), hp₁, hs₁]
  have hp₃ : p.phase 3 = i₃ := by rw [path_succ p (by decide : 2 < 8), hp₂, hs₂]
  have hp₄ : p.phase 4 = i₄ := by rw [path_succ p (by decide : 3 < 8), hp₃, hs₃]
  have hp₅ : p.phase 5 = i₅ := by rw [path_succ p (by decide : 4 < 8), hp₄, hs₄]
  have hp₆ : p.phase 6 = i₆ := by rw [path_succ p (by decide : 5 < 8), hp₅, hs₅]
  have hp₇ : p.phase 7 = i₇ := by rw [path_succ p (by decide : 6 < 8), hp₆, hs₆]
  have hp₈ : p.phase 8 = i₈ := by rw [path_succ p (by decide : 7 < 8), hp₇, hs₇]
  have step (r : Nat) (hr : r < 8) : p.pos w (r + 1) = move (p.pos w r) (outDir w (p.phase r)) :=
    p.pos_step hr
  have hx₁ : p.pos w 1 = move (p.pos w 0) d₀ := by rw [step 0 (by decide), hp₀, hd₀]
  have hx₂ : p.pos w 2 = move (move (p.pos w 0) d₀) d₁ := by
    rw [step 1 (by decide), hp₁, hd₁, hx₁]
  have hx₃ : p.pos w 3 = move (move (move (p.pos w 0) d₀) d₁) d₂ := by
    rw [step 2 (by decide), hp₂, hd₂, hx₂]
  have hx₄ : p.pos w 4 = move (move (move (move (p.pos w 0) d₀) d₁) d₂) d₃ := by
    rw [step 3 (by decide), hp₃, hd₃, hx₃]
  have hx₅ : p.pos w 5 = move (move (move (move (move (p.pos w 0) d₀) d₁) d₂) d₃) d₄ := by
    rw [step 4 (by decide), hp₄, hd₄, hx₄]
  have hx₆ : p.pos w 6 =
      move (move (move (move (move (move (p.pos w 0) d₀) d₁) d₂) d₃) d₄) d₅ := by
    rw [step 5 (by decide), hp₅, hd₅, hx₅]
  have hx₇ : p.pos w 7 =
      move (move (move (move (move (move (move (p.pos w 0) d₀) d₁) d₂) d₃) d₄) d₅) d₆ := by
    rw [step 6 (by decide), hp₆, hd₆, hx₆]
  have hx₈ : p.pos w 8 = walk (p.pos w 0) [d₀, d₁, d₂, d₃, d₄, d₅, d₆, d₇] := by
    rw [step 7 (by decide), hp₇, hd₇, hx₇]; rfl
  obtain ⟨hclose, hfirst⟩ := (firstReturn_iff _ _).mp (hret (p.pos w 0))
  have hh := p.firstReturn_rank hd (by decide : 0 < 8) (hx₈.trans hclose) (by
    intro r hr hr'
    rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [hx₁, List.take, walk] using hfirst 1 (by decide) (by simp)
    · simpa only [hx₂, List.take, walk] using hfirst 2 (by decide) (by simp)
    · simpa only [hx₃, List.take, walk] using hfirst 3 (by decide) (by simp)
    · simpa only [hx₄, List.take, walk] using hfirst 4 (by decide) (by simp)
    · simpa only [hx₅, List.take, walk] using hfirst 5 (by decide) (by simp)
    · simpa only [hx₆, List.take, walk] using hfirst 6 (by decide) (by simp)
    · simpa only [hx₇, List.take, walk] using hfirst 7 (by decide) (by simp))
  simpa only [hp₀, hp₈] using hh

private theorem getElem_of_getElem? {α : Type} {l : List α} {k : Nat} {a : α}
    (hk : k < l.length) (h : l[k]? = some a) : l[k] = a :=
  Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans h)

private theorem succ_of_departure_port {P r k : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    {L : Int} {d : Direction}
    (hr : r < (layerPhases P w L).length)
    (hdep : (trueIdx (portWord hd L (fun j => decide (outDir w j = d))))[k]? = some r) :
    let i := phaseAtRank hd L ⟨r, hr⟩
    outDir w i = d ∧
    UnitDiagonalMatching.succ P i ∈ layerPhases P w (L + UnitDiagonalMatching.layerStep d) ∧
    (trueIdx (portWord hd (L + UnitDiagonalMatching.layerStep d)
      (fun j => decide (inDir w j = d))))[k]? =
      some (stableRank P w (UnitDiagonalMatching.succ P i)) := by
  intro i
  have him : i ∈ layerPhases P w L := phaseAtRank_mem hd L ⟨r, hr⟩
  have hir : stableRank P w i = r := phaseAtRank_rank hd L ⟨r, hr⟩
  have hmem : r ∈ trueIdx (portWord hd L (fun j => decide (outDir w j = d))) :=
    List.mem_iff_getElem?.mpr ⟨k, hdep⟩
  have htrue : (portWord hd L (fun j => decide (outDir w j = d)))[r]? = some true :=
    mem_trueIdx.mp hmem
  have hget : (portWord hd L (fun j => decide (outDir w j = d)))[r]? =
      some (decide (outDir w i = d)) := portWord_get hd L _ ⟨r, hr⟩
  have hout : outDir w i = d := by
    have hdec : decide (outDir w i = d) = true := Option.some.inj (hget.symm.trans htrue)
    exact of_decide_eq_true hdec
  obtain ⟨hiP, hiL⟩ := mem_layerPhases.mp him
  have hid : i ∈ UnitDiagonalMatching.departures P w L d :=
    UnitDiagonalMatching.mem_departures.mpr ⟨hiP, hiL, hout⟩
  have harr := (UnitDiagonalMatching.successor_mem_iff h.1 hd hiP).mpr hid
  obtain ⟨hsP, hsL, _⟩ := UnitDiagonalMatching.mem_arrivals.mp harr
  have hidx := successor_port_index h hd hid (by rw [hir]; exact hdep)
  exact ⟨hout, mem_layerPhases.mpr ⟨hsP, hsL⟩, hidx⟩

private theorem succ_phaseAtRank_of_port_match {P r s k : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    {L L' : Int} {d : Direction}
    (hL : L + UnitDiagonalMatching.layerStep d = L')
    (hr : r < (layerPhases P w L).length)
    (hs : s < (layerPhases P w L').length)
    (hdep : (trueIdx (portWord hd L (fun j => decide (outDir w j = d))))[k]? = some r)
    (harr : (trueIdx (portWord hd L' (fun j => decide (inDir w j = d))))[k]? = some s) :
    outDir w (phaseAtRank hd L ⟨r, hr⟩) = d ∧
    UnitDiagonalMatching.succ P (phaseAtRank hd L ⟨r, hr⟩) = phaseAtRank hd L' ⟨s, hs⟩ := by
  subst hL
  obtain ⟨hout, hmem, hidx⟩ := succ_of_departure_port h hd hr hdep
  have hrank : stableRank P w (UnitDiagonalMatching.succ P (phaseAtRank hd L ⟨r, hr⟩)) = s :=
    Option.some.inj (hidx.symm.trans harr)
  refine ⟨hout, ?_⟩
  exact stableRank_injective_on_layer hd hmem (phaseAtRank_mem hd _ ⟨s, hs⟩)
    (hrank.trans (phaseAtRank_rank hd _ ⟨s, hs⟩).symm)

private theorem pred_of_arrival_port {P r k : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    {L L' : Int} {d : Direction}
    (hL : L + UnitDiagonalMatching.layerStep d = L')
    (hr : r < (layerPhases P w L').length)
    (harr : (trueIdx (portWord hd L' (fun m => decide (inDir w m = d))))[k]? = some r) :
    let j := phaseAtRank hd L' ⟨r, hr⟩
    let i := UnitDiagonalMatching.pred P j
    i ∈ layerPhases P w L ∧
    UnitDiagonalMatching.succ P i = j ∧
    outDir w i = d ∧
    (trueIdx (portWord hd L (fun m => decide (outDir w m = d))))[k]? =
      some (stableRank P w i) := by
  subst hL
  intro j i
  have hjm : j ∈ layerPhases P w (L + UnitDiagonalMatching.layerStep d) :=
    phaseAtRank_mem hd _ ⟨r, hr⟩
  have hjr : stableRank P w j = r := phaseAtRank_rank hd _ ⟨r, hr⟩
  have hmem : r ∈ trueIdx (portWord hd (L + UnitDiagonalMatching.layerStep d)
      (fun m => decide (inDir w m = d))) :=
    List.mem_iff_getElem?.mpr ⟨k, harr⟩
  have htrue : (portWord hd (L + UnitDiagonalMatching.layerStep d)
      (fun m => decide (inDir w m = d)))[r]? = some true :=
    mem_trueIdx.mp hmem
  have hget : (portWord hd (L + UnitDiagonalMatching.layerStep d)
      (fun m => decide (inDir w m = d)))[r]? = some (decide (inDir w j = d)) :=
    portWord_get hd _ _ ⟨r, hr⟩
  have hin : inDir w j = d := by
    have hdec : decide (inDir w j = d) = true := Option.some.inj (hget.symm.trans htrue)
    exact of_decide_eq_true hdec
  obtain ⟨hjP, hjL⟩ := mem_layerPhases.mp hjm
  have hja : j ∈ UnitDiagonalMatching.arrivals P w (L + UnitDiagonalMatching.layerStep d) d :=
    UnitDiagonalMatching.mem_arrivals.mpr ⟨hjP, hjL, hin⟩
  have hdep := UnitDiagonalMatching.predecessor_mem h.1 hd hja
  obtain ⟨hiP, hiL, hout⟩ := UnitDiagonalMatching.mem_departures.mp hdep
  have hsucc : UnitDiagonalMatching.succ P i = j := UnitDiagonalMatching.succ_pred hjP
  have hidx := predecessor_port_index h hd hja (by rw [hjr]; exact harr)
  exact ⟨mem_layerPhases.mpr ⟨hiP, hiL⟩, hsucc, hout, hidx⟩

/-! ## L23: Layer A and B port lists and fixed paths above B -/

theorem first_inner_port_lists {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    (layerPhases P w (topLayer P w - 1)).length = 4 ∧
    trueIdx (portWord hd (topLayer P w - 1) (fun i => decide (inDir w i = .north))) = [1, 2, 3] ∧
    trueIdx (portWord hd (topLayer P w - 1) (fun i => decide (outDir w i = .west))) = [0, 1, 3] := by
  have hA := (second_inner_two_words h hd).1
  have hlen : (layerPhases P w (topLayer P w - 1)).length = 4 := by
    have hl := portWord_length hd (topLayer P w - 1) (LangtonsAnt.alpha w)
    change (alphaWord hd (topLayer P w - 1)).length = _ at hl
    rw [hA] at hl
    simpa using hl.symm
  have hNA : portWord hd (topLayer P w - 1) (fun i => decide (inDir w i = .north)) =
      (alphaWord hd (topLayer P w - 1)).map (!·) := incoming_portWord h hd 1 false
  have hWA : portWord hd (topLayer P w - 1) (fun i => decide (outDir w i = .west)) =
      (betaWord hd (topLayer P w - 1)).map (!·) := outgoing_portWord h hd 1 false
  have hβA : betaWord hd (topLayer P w - 1) = beta (alphaWord hd (topLayer P w - 1)) true := by
    have hb := betaWord_eq h hd (topLayer P w - 1)
    have he : topLayer P w - (topLayer P w - 1) = 1 := by omega
    rw [he] at hb
    exact hb
  refine ⟨hlen, ?_, ?_⟩
  · rw [hNA, hA]; decide
  · rw [hWA, hβA, hA]; decide

theorem second_inner_port_lists {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    8 ≤ (layerPhases P w (topLayer P w - 2)).length ∧
    trueIdx (portWord hd (topLayer P w - 2) (fun i => decide (inDir w i = .west))) = [4, 5, 7] ∧
    trueIdx (portWord hd (topLayer P w - 2) (fun i => decide (outDir w i = .north))) = [1, 3, 4] ∧
    (trueIdx (portWord hd (topLayer P w - 2) (fun i => decide (outDir w i = .south))) =
        [0, 2, 5, 6, 7] ∨
      trueIdx (portWord hd (topLayer P w - 2) (fun i => decide (outDir w i = .south))) =
        [0, 2, 5, 6, 7, 8]) ∧
    (trueIdx (portWord hd (topLayer P w - 2) (fun i => decide (inDir w i = .east))) =
        [0, 1, 2, 3, 6] ∨
      trueIdx (portWord hd (topLayer P w - 2) (fun i => decide (inDir w i = .east))) =
        [0, 1, 2, 3, 6, 8]) := by
  have hB := (second_inner_two_words h hd).2
  have hβB : betaWord hd (topLayer P w - 2) = beta (alphaWord hd (topLayer P w - 2)) false := by
    have hb := betaWord_eq h hd (topLayer P w - 2)
    have he : topLayer P w - (topLayer P w - 2) = 2 := by omega
    rw [he] at hb
    exact hb
  have hWB : portWord hd (topLayer P w - 2) (fun i => decide (inDir w i = .west)) =
      alphaWord hd (topLayer P w - 2) := incoming_portWord h hd 2 true
  have hEB : portWord hd (topLayer P w - 2) (fun i => decide (inDir w i = .east)) =
      (alphaWord hd (topLayer P w - 2)).map (!·) := incoming_portWord h hd 2 false
  have hNB : portWord hd (topLayer P w - 2) (fun i => decide (outDir w i = .north)) =
      betaWord hd (topLayer P w - 2) := outgoing_portWord h hd 2 true
  have hSB : portWord hd (topLayer P w - 2) (fun i => decide (outDir w i = .south)) =
      (betaWord hd (topLayer P w - 2)).map (!·) := outgoing_portWord h hd 2 false
  have hl := portWord_length hd (topLayer P w - 2) (LangtonsAnt.alpha w)
  change (alphaWord hd (topLayer P w - 2)).length = _ at hl
  rcases hB with h8 | h9
  · refine ⟨?_, ?_, ?_, Or.inl ?_, Or.inl ?_⟩
    · rw [h8] at hl; simp [W8] at hl; omega
    · rw [hWB, h8]; exact W8_trueIdx
    · rw [hNB, hβB, h8]; exact W8_beta_trueIdx
    · rw [hSB, hβB, h8]; exact W8_beta_falseIdx
    · rw [hEB, h8]; exact W8_falseIdx
  · refine ⟨?_, ?_, ?_, Or.inr ?_, Or.inr ?_⟩
    · rw [h9] at hl; simp [W9] at hl; omega
    · rw [hWB, h9]; exact W9_trueIdx
    · rw [hNB, hβB, h9]; exact W9_beta_trueIdx
    · rw [hSB, hβB, h9]; exact W9_beta_falseIdx
    · rw [hEB, h9]; exact W9_falseIdx

/-- L23: the fixed actual successor paths `B₁ → A₁ → B₅` and
`B₃ → A₂ → T → A₀ → B₄ → A₃ → B₇` above layer B. -/
theorem second_inner_upper_paths {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hLA : (layerPhases P w (topLayer P w - 1)).length = 4)
    (hLB : 8 ≤ (layerPhases P w (topLayer P w - 2)).length) :
    let a₀ := phaseAtRank hd (topLayer P w - 1) ⟨0, by omega⟩
    let a₁ := phaseAtRank hd (topLayer P w - 1) ⟨1, by omega⟩
    let a₂ := phaseAtRank hd (topLayer P w - 1) ⟨2, by omega⟩
    let a₃ := phaseAtRank hd (topLayer P w - 1) ⟨3, by omega⟩
    let b₁ := phaseAtRank hd (topLayer P w - 2) ⟨1, by omega⟩
    let b₃ := phaseAtRank hd (topLayer P w - 2) ⟨3, by omega⟩
    let b₄ := phaseAtRank hd (topLayer P w - 2) ⟨4, by omega⟩
    let b₅ := phaseAtRank hd (topLayer P w - 2) ⟨5, by omega⟩
    let b₇ := phaseAtRank hd (topLayer P w - 2) ⟨7, by omega⟩
    ∃ t,
      (UnitDiagonalMatching.succ P b₁ = a₁ ∧ outDir w b₁ = .north) ∧
      (UnitDiagonalMatching.succ P a₁ = b₅ ∧ outDir w a₁ = .west) ∧
      (UnitDiagonalMatching.succ P b₃ = a₂ ∧ outDir w b₃ = .north) ∧
      (UnitDiagonalMatching.succ P a₂ = t ∧ outDir w a₂ = .east) ∧
      (UnitDiagonalMatching.succ P t = a₀ ∧ outDir w t = .south) ∧
      (UnitDiagonalMatching.succ P a₀ = b₄ ∧ outDir w a₀ = .west) ∧
      (UnitDiagonalMatching.succ P b₄ = a₃ ∧ outDir w b₄ = .north) ∧
      (UnitDiagonalMatching.succ P a₃ = b₇ ∧ outDir w a₃ = .west) := by
  intro a₀ a₁ a₂ a₃ b₁ b₃ b₄ b₅ b₇
  obtain ⟨_, hNA, hWA⟩ := first_inner_port_lists h hd
  obtain ⟨_, hWB, hNB, _, _⟩ := second_inner_port_lists h hd
  have hLup : topLayer P w - 2 + UnitDiagonalMatching.layerStep .north = topLayer P w - 1 := by
    simp only [UnitDiagonalMatching.layerStep]; omega
  have hLdown : topLayer P w - 1 + UnitDiagonalMatching.layerStep .west = topLayer P w - 2 := by
    simp only [UnitDiagonalMatching.layerStep]; omega
  have hB1A1 := succ_phaseAtRank_of_port_match h hd hLup
    (r := 1) (s := 1) (k := 0) (by omega) (by omega)
    (by rw [hNB]; rfl) (by rw [hNA]; rfl)
  have hA1B5 := succ_phaseAtRank_of_port_match h hd hLdown
    (r := 1) (s := 5) (k := 1) (by omega) (by omega)
    (by rw [hWA]; rfl) (by rw [hWB]; rfl)
  have hB3A2 := succ_phaseAtRank_of_port_match h hd hLup
    (r := 3) (s := 2) (k := 1) (by omega) (by omega)
    (by rw [hNB]; rfl) (by rw [hNA]; rfl)
  have hA0B4 := succ_phaseAtRank_of_port_match h hd hLdown
    (r := 0) (s := 4) (k := 0) (by omega) (by omega)
    (by rw [hWA]; rfl) (by rw [hWB]; rfl)
  have hB4A3 := succ_phaseAtRank_of_port_match h hd hLup
    (r := 4) (s := 3) (k := 2) (by omega) (by omega)
    (by rw [hNB]; rfl) (by rw [hNA]; rfl)
  have hA3B7 := succ_phaseAtRank_of_port_match h hd hLdown
    (r := 3) (s := 7) (k := 2) (by omega) (by omega)
    (by rw [hWA]; rfl) (by rw [hWB]; rfl)
  obtain ⟨a₂', t, a₀', ha₂', ha₀', hr₂', hr₀', hst₂, hst₀, _, ho₂', hot, _⟩ :=
    first_inner_events h hd
  have ha₂_eq : a₂' = a₂ :=
    stableRank_injective_on_layer hd ha₂' (phaseAtRank_mem hd (topLayer P w - 1) ⟨2, by omega⟩)
      (hr₂'.trans (phaseAtRank_rank hd (topLayer P w - 1) ⟨2, by omega⟩).symm)
  have ha₀_eq : a₀' = a₀ :=
    stableRank_injective_on_layer hd ha₀' (phaseAtRank_mem hd (topLayer P w - 1) ⟨0, by omega⟩)
      (hr₀'.trans (phaseAtRank_rank hd (topLayer P w - 1) ⟨0, by omega⟩).symm)
  subst ha₂_eq
  subst ha₀_eq
  exact ⟨t,
    ⟨hB1A1.2, hB1A1.1⟩, ⟨hA1B5.2, hA1B5.1⟩,
    ⟨hB3A2.2, hB3A2.1⟩, ⟨hst₂, ho₂'⟩, ⟨hst₀, hot⟩,
    ⟨hA0B4.2, hA0B4.1⟩, ⟨hB4A3.2, hB4A3.1⟩, ⟨hA3B7.2, hA3B7.1⟩⟩

/-! ## L24: Layer C port lengths and B ↔ C matching -/

/-- L24 (lengths): layer C has at least five upper arrivals and five upper departures. -/
theorem third_inner_lengths {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) :
    5 ≤ (trueIdx (alphaWord hd (topLayer P w - 3))).length ∧
    5 ≤ (trueIdx (betaWord hd (topLayer P w - 3))).length := by
  have hB := (second_inner_two_words h hd).2
  have hc := cut_down_count h hd (topLayer P w - 2)
  have he : topLayer P w - 2 - 1 = topLayer P w - 3 := by omega
  rw [he] at hc
  have hβB : betaWord hd (topLayer P w - 2) = beta (alphaWord hd (topLayer P w - 2)) false := by
    have hb := betaWord_eq h hd (topLayer P w - 2)
    have he2 : topLayer P w - (topLayer P w - 2) = 2 := by omega
    rw [he2] at hb
    exact hb
  have hl := portWord_length hd (topLayer P w - 2) (LangtonsAnt.alpha w)
  change (alphaWord hd (topLayer P w - 2)).length = _ at hl
  have hcount : 5 ≤ countTrue (alphaWord hd (topLayer P w - 3)) := by
    rcases hB with h8 | h9
    · rw [hβB, h8] at hc
      rw [h8] at hl
      have h3 : countTrue (beta W8 false) = 3 := by decide
      have hlen8 : W8.length = 8 := rfl
      omega
    · rw [hβB, h9] at hc
      rw [h9] at hl
      have h3 : countTrue (beta W9 false) = 3 := by decide
      have hlen9 : W9.length = 9 := rfl
      omega
  have heq := layer_counts_eq h hd (by omega : topLayer P w - 3 ≤ topLayer P w)
  rw [trueIdx_length, trueIdx_length, ← heq]
  exact ⟨hcount, hcount⟩

/-- L24 (downward matching B → C): the first five downward departures of B
(`[0, 2, 5, 6, 7]`) leave south into the first five upper arrivals `p[0..4]` of C. -/
theorem second_to_third_port {P k r : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hr : r < (layerPhases P w (topLayer P w - 2)).length)
    (hk : ([0, 2, 5, 6, 7] : List Nat)[k]? = some r) :
    let b := phaseAtRank hd (topLayer P w - 2) ⟨r, hr⟩
    outDir w b = .south ∧
    UnitDiagonalMatching.succ P b ∈ layerPhases P w (topLayer P w - 3) ∧
    (trueIdx (alphaWord hd (topLayer P w - 3)))[k]? =
      some (stableRank P w (UnitDiagonalMatching.succ P b)) := by
  obtain ⟨_, _, _, hSB, _⟩ := second_inner_port_lists h hd
  have hdep : (trueIdx (portWord hd (topLayer P w - 2)
      (fun j => decide (outDir w j = .south))))[k]? = some r := by
    rcases hSB with h5 | h6
    · rw [h5]; exact hk
    · rw [h6]
      have hlt : k < ([0, 2, 5, 6, 7] : List Nat).length := lt_length_of_getElem? hk
      change ([0, 2, 5, 6, 7] ++ [8])[k]? = some r
      rw [List.getElem?_append_left hlt]
      exact hk
  have hL : topLayer P w - 2 + UnitDiagonalMatching.layerStep .south = topLayer P w - 3 := by
    simp only [UnitDiagonalMatching.layerStep]; omega
  have hSC : portWord hd (topLayer P w - 3) (fun j => decide (inDir w j = .south)) =
      alphaWord hd (topLayer P w - 3) := incoming_portWord h hd 3 true
  have hs := succ_of_departure_port h hd hr hdep
  rw [hL, hSC] at hs
  exact hs

/-- L24 (upward matching C → B): the first five upper departures `q[0..4]` of C
leave east into the first five from-below arrivals `[0, 1, 2, 3, 6]` of B. -/
theorem third_to_second_port {P k r : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hr : r < (layerPhases P w (topLayer P w - 2)).length)
    (hk : ([0, 1, 2, 3, 6] : List Nat)[k]? = some r) :
    let b := phaseAtRank hd (topLayer P w - 2) ⟨r, hr⟩
    let c := UnitDiagonalMatching.pred P b
    c ∈ layerPhases P w (topLayer P w - 3) ∧
    UnitDiagonalMatching.succ P c = b ∧
    outDir w c = .east ∧
    (trueIdx (betaWord hd (topLayer P w - 3)))[k]? = some (stableRank P w c) := by
  obtain ⟨_, _, _, _, hEB⟩ := second_inner_port_lists h hd
  have hL : topLayer P w - 3 + UnitDiagonalMatching.layerStep .east = topLayer P w - 2 := by
    simp only [UnitDiagonalMatching.layerStep]; omega
  have harr : (trueIdx (portWord hd (topLayer P w - 2)
      (fun j => decide (inDir w j = .east))))[k]? = some r := by
    rcases hEB with h5 | h6
    · rw [h5]; exact hk
    · rw [h6]
      have hlt : k < ([0, 1, 2, 3, 6] : List Nat).length := lt_length_of_getElem? hk
      change ([0, 1, 2, 3, 6] ++ [8])[k]? = some r
      rw [List.getElem?_append_left hlt]
      exact hk
  have hEC : portWord hd (topLayer P w - 3) (fun j => decide (outDir w j = .east)) =
      betaWord hd (topLayer P w - 3) := outgoing_portWord h hd 3 true
  have hp := pred_of_arrival_port h hd hL hr harr
  rw [hEC] at hp
  exact hp

/-! ## L25–L27: First-return constraints on layer C -/

/-- L25: the `ENWS` and `ENESWNWS` first returns give `p[2] = q[1] + 1` and
`p[4] = q[3] + 1` on layer C. -/
theorem third_inner_returns {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hlp : 5 ≤ (trueIdx (alphaWord hd (topLayer P w - 3))).length)
    (hlq : 5 ≤ (trueIdx (betaWord hd (topLayer P w - 3))).length) :
    (trueIdx (alphaWord hd (topLayer P w - 3)))[2] =
      (trueIdx (betaWord hd (topLayer P w - 3)))[1] + 1 ∧
    (trueIdx (alphaWord hd (topLayer P w - 3)))[4] =
      (trueIdx (betaWord hd (topLayer P w - 3)))[3] + 1 := by
  have hLA := (first_inner_port_lists h hd).1
  have hLB := (second_inner_port_lists h hd).1
  obtain ⟨t, ⟨hsB1, hoB1⟩, ⟨hsA1, hoA1⟩, ⟨hsB3, hoB3⟩, ⟨hsA2, hoA2⟩, ⟨hst, hot⟩,
    ⟨hsA0, hoA0⟩, ⟨hsB4, hoB4⟩, ⟨hsA3, hoA3⟩⟩ := second_inner_upper_paths h hd hLA hLB
  -- Return 1 (ENWS): C_{q₁} → B₁ → A₁ → B₅ → C_{p₂}
  obtain ⟨hc1m, hsc1, hoc1, hq1⟩ := third_to_second_port h hd (k := 1) (r := 1) (by omega) rfl
  obtain ⟨hoB5, _, hp2⟩ := second_to_third_port h hd (k := 2) (r := 5) (by omega) rfl
  have hret1 := four_step_return_rank hd (mem_layerPhases.mp hc1m).1 hsc1 hsB1 hsA1 rfl
    .east .north .west .south hoc1 hoB1 hoA1 hoB5 firstReturn_ENWS
  have h1 : (trueIdx (alphaWord hd (topLayer P w - 3)))[2] =
      (trueIdx (betaWord hd (topLayer P w - 3)))[1] + 1 := by
    rw [getElem_of_getElem? (by omega) hp2, getElem_of_getElem? (by omega) hq1]
    exact hret1
  -- Return 2 (ENESWNWS): C_{q₃} → B₃ → A₂ → T → A₀ → B₄ → A₃ → B₇ → C_{p₄}
  obtain ⟨hc3m, hsc3, hoc3, hq3⟩ := third_to_second_port h hd (k := 3) (r := 3) (by omega) rfl
  obtain ⟨hoB7, _, hp4⟩ := second_to_third_port h hd (k := 4) (r := 7) (by omega) rfl
  have hret2 := eight_step_return_rank hd (mem_layerPhases.mp hc3m).1
    hsc3 hsB3 hsA2 hst hsA0 hsB4 hsA3 rfl
    .east .north .east .south .west .north .west .south
    hoc3 hoB3 hoA2 hot hoA0 hoB4 hoA3 hoB7 firstReturn_ENESWNWS
  have h2 : (trueIdx (alphaWord hd (topLayer P w - 3)))[4] =
      (trueIdx (betaWord hd (topLayer P w - 3)))[3] + 1 := by
    rw [getElem_of_getElem? (by omega) hp4, getElem_of_getElem? (by omega) hq3]
    exact hret2
  exact ⟨h1, h2⟩

/-- L26: `p[1] ≠ q[1]` on layer C; otherwise the `SENW` return `B₂ → C → B₁ → A₁ → B₅`
would force `5 = 2 + 1`. -/
theorem third_inner_forbid_bridge1 {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hlp : 5 ≤ (trueIdx (alphaWord hd (topLayer P w - 3))).length)
    (hlq : 5 ≤ (trueIdx (betaWord hd (topLayer P w - 3))).length) :
    (trueIdx (alphaWord hd (topLayer P w - 3)))[1] ≠
      (trueIdx (betaWord hd (topLayer P w - 3)))[1] := by
  intro heq
  have hLA := (first_inner_port_lists h hd).1
  have hLB := (second_inner_port_lists h hd).1
  obtain ⟨_, ⟨hsB1, hoB1⟩, ⟨hsA1, hoA1⟩, _⟩ := second_inner_upper_paths h hd hLA hLB
  obtain ⟨hoB2, hsb2m, hp1⟩ := second_to_third_port h hd (k := 1) (r := 2) (by omega) rfl
  obtain ⟨hc1m, hsc1, hoc1, hq1⟩ := third_to_second_port h hd (k := 1) (r := 1) (by omega) rfl
  have hrank : stableRank P w (UnitDiagonalMatching.succ P (phaseAtRank hd (topLayer P w - 2) ⟨2, by omega⟩)) =
      stableRank P w (UnitDiagonalMatching.pred P (phaseAtRank hd (topLayer P w - 2) ⟨1, by omega⟩)) := by
    rw [← getElem_of_getElem? (by omega) hp1, ← getElem_of_getElem? (by omega) hq1]
    exact heq
  have hbridge : UnitDiagonalMatching.succ P (phaseAtRank hd (topLayer P w - 2) ⟨2, by omega⟩) =
      UnitDiagonalMatching.pred P (phaseAtRank hd (topLayer P w - 2) ⟨1, by omega⟩) :=
    stableRank_injective_on_layer hd hsb2m hc1m hrank
  have hb2P : phaseAtRank hd (topLayer P w - 2) ⟨2, by omega⟩ < P :=
    (mem_layerPhases.mp (phaseAtRank_mem hd (topLayer P w - 2) ⟨2, by omega⟩)).1
  have hret := four_step_return_rank hd hb2P hbridge hsc1 hsB1 hsA1
    .south .east .north .west hoB2 hoc1 hoB1 hoA1 firstReturn_SENW
  simp only [phaseAtRank_rank] at hret
  omega

/-- L27: `p[4] ≠ q[4]` on layer C; otherwise the `NWSE` return `B₄ → A₃ → B₇ → C → B₆`
would force `6 = 4 + 1`. -/
theorem third_inner_forbid_bridge2 {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1))
    (hlp : 5 ≤ (trueIdx (alphaWord hd (topLayer P w - 3))).length)
    (hlq : 5 ≤ (trueIdx (betaWord hd (topLayer P w - 3))).length) :
    (trueIdx (alphaWord hd (topLayer P w - 3)))[4] ≠
      (trueIdx (betaWord hd (topLayer P w - 3)))[4] := by
  intro heq
  have hLA := (first_inner_port_lists h hd).1
  have hLB := (second_inner_port_lists h hd).1
  obtain ⟨_, _, _, _, _, _, _, ⟨hsB4, hoB4⟩, ⟨hsA3, hoA3⟩⟩ :=
    second_inner_upper_paths h hd hLA hLB
  obtain ⟨hoB7, hsb7m, hp4⟩ := second_to_third_port h hd (k := 4) (r := 7) (by omega) rfl
  obtain ⟨hc4m, hsc4, hoc4, hq4⟩ := third_to_second_port h hd (k := 4) (r := 6) (by omega) rfl
  have hrank : stableRank P w (UnitDiagonalMatching.succ P (phaseAtRank hd (topLayer P w - 2) ⟨7, by omega⟩)) =
      stableRank P w (UnitDiagonalMatching.pred P (phaseAtRank hd (topLayer P w - 2) ⟨6, by omega⟩)) := by
    rw [← getElem_of_getElem? (by omega) hp4, ← getElem_of_getElem? (by omega) hq4]
    exact heq
  have hbridge : UnitDiagonalMatching.succ P (phaseAtRank hd (topLayer P w - 2) ⟨7, by omega⟩) =
      UnitDiagonalMatching.pred P (phaseAtRank hd (topLayer P w - 2) ⟨6, by omega⟩) :=
    stableRank_injective_on_layer hd hsb7m hc4m hrank
  have hb4P : phaseAtRank hd (topLayer P w - 2) ⟨4, by omega⟩ < P :=
    (mem_layerPhases.mp (phaseAtRank_mem hd (topLayer P w - 2) ⟨4, by omega⟩)).1
  have hret := four_step_return_rank hd hb4P hsB4 hsA3 hbridge hsc4
    .north .west .south .east hoB4 hoA3 hoB7 hoc4 firstReturn_NWSE
  simp only [phaseAtRank_rank] at hret
  omega

/-! ## L29: Contradiction via `interleave_bridge` on layer C -/

/-- L29: a consistent word cannot have full displacement `(1, -1)`, because layer C's
upper port lists satisfy `interleave_bridge`, forcing one of the two forbidden bridges. -/
theorem third_inner_impossible {P : Nat} {w : Nat → Bool}
    (h : ConsistentWord P w) (hd : wordDrift P w = (1, -1)) : False := by
  let LC := topLayer P w - 3
  let αC := alphaWord hd LC
  let βC := betaWord hd LC
  let p := trueIdx αC
  let q := trueIdx βC
  let n := (layerPhases P w LC).length
  have hlenα : αC.length = n := portWord_length hd LC (LangtonsAnt.alpha w)
  have hlenβ : βC.length = n := portWord_length hd LC (LangtonsAnt.beta w)
  have hβC : βC = beta αC true := by
    have hb := betaWord_eq h hd LC
    have he : topLayer P w - LC = 3 := by dsimp [LC]; omega
    rw [he] at hb
    exact hb
  have hpn : ∀ x ∈ p, x < n := fun x hx => by
    rw [← hlenα]
    exact lt_length_of_getElem? (mem_trueIdx.mp hx)
  have hqn : ∀ x ∈ q, x < n := fun x hx => by
    rw [← hlenβ]
    exact lt_length_of_getElem? (mem_trueIdx.mp hx)
  obtain ⟨hlp, hlq⟩ := third_inner_lengths h hd
  have heven : ∀ x, x < n → x % 2 = 0 → (x ∈ p ↔ x ∉ q) := by
    intro x hxn hxe
    have hxα : x < αC.length := by omega
    have hget : αC[x]? = some αC[x] := List.getElem?_eq_getElem hxα
    have hdec : decide (x % 2 = 1) = false := decide_eq_false (by omega)
    have hgetβ : βC[x]? = some (!αC[x]) := by
      rw [hβC, beta_spec, hget, hdec]
      cases αC[x] <;> rfl
    simp only [p, q, mem_trueIdx, hget, hgetβ, Option.some.injEq]
    cases αC[x] <;> simp
  have hodd : ∀ x, x < n → x % 2 = 1 → (x ∈ p ↔ x ∈ q) := by
    intro x hxn hxo
    have hxα : x < αC.length := by omega
    have hget : αC[x]? = some αC[x] := List.getElem?_eq_getElem hxα
    have hdec : decide (x % 2 = 1) = true := decide_eq_true hxo
    have hgetβ : βC[x]? = some αC[x] := by
      rw [hβC, beta_spec, hget, hdec]
      cases αC[x] <;> rfl
    simp only [p, q, mem_trueIdx, hget, hgetβ]
  obtain ⟨h2, h4⟩ := third_inner_returns h hd hlp hlq
  have hbridge := interleave_bridge p q n (pairwise_trueIdx αC) (pairwise_trueIdx βC)
    hpn hqn hlp hlq heven hodd h2 h4
  rcases hbridge with h1 | h4'
  · exact third_inner_forbid_bridge1 h hd hlp hlq h1
  · exact third_inner_forbid_bridge2 h hd hlp hlq h4'

end UnitDiagonal
