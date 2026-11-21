import FirstContact

namespace LangtonsAnt

theorem perturb_involutive (mask : Board) (s : State) : perturb mask (perturb mask s) = s := by
  have hb : (fun p => (s.board p ^^ mask p) ^^ mask p) = s.board := by
    funext p
    cases s.board p <;> cases mask p <;> rfl
  cases s
  simp only [perturb, hb]

theorem perturb_translate (mask : Board) (s : State) (v : Point) :
    translate v (perturb mask s) = perturb (fun p => mask (subPoint p v)) (translate v s) := by
  rfl

/-- Keep all unvisited initial defects explicit while coupling the generated history. -/
theorem AgreesBelow.run_perturb {cut : Int} {s t : State} {mask : Board}
    (h : AgreesBelow cut s (LangtonsAnt.perturb mask t)) (n : Nat)
    (hb : forall j, j < n -> weight (LangtonsAnt.run t j).pos <= cut)
    (ha : forall j, j < n -> mask (LangtonsAnt.run t j).pos = false) :
    AgreesBelow cut (LangtonsAnt.run s n) (LangtonsAnt.perturb mask (LangtonsAnt.run t n)) := by
  have ht := run_perturb_avoids mask t n ha
  have hr := h.run n (by
    intro j hj
    have he := run_perturb_avoids mask t j (fun i hi => ha i (by omega))
    rw [he]
    exact hb j hj)
  rw [ht] at hr
  exact hr

/-- Restoring a known mask turns agreement with a masked board into ordinary agreement. -/
theorem AgreesBelow.unperturb {cut : Int} {s t : State} {mask : Board}
    (h : AgreesBelow cut s (LangtonsAnt.perturb mask t)) : AgreesBelow cut (LangtonsAnt.perturb mask s) t := by
  have hh := h.perturb mask
  rw [perturb_involutive] at hh
  exact hh

end LangtonsAnt
