import DriftRank

namespace LangtonsAnt.PersistA.TwoLaneCycle

abbrev Node := Int × Int

def Edge (a b : Node) : Prop :=
  (b.1 = a.1 + 1 ∨ b.1 = a.1 - 1) ∧
    b.2 = if a.1 % 2 = 0 then 1 - a.2 else a.2

theorem two_step_lane {a b c : Node} (hab : Edge a b) (hbc : Edge b c) :
    c.2 = 1 - a.2 := by
  rcases hab with ⟨hab, hrab⟩
  rcases hbc with ⟨hbc, hrbc⟩
  by_cases ha : a.1 % 2 = 0
  · have hb : b.1 % 2 ≠ 0 := by omega
    simp only [ha, hb, ite_true, ite_false] at hrab hrbc
    omega
  · have hb : b.1 % 2 = 0 := by omega
    simp only [ha, hb, ite_true, ite_false] at hrab hrbc
    omega

theorem maximal_turn {a b c : Node} (hab : Edge a b) (hbc : Edge b c)
    (ha : a.1 ≤ b.1) (hc : c.1 ≤ b.1) :
    a.1 = b.1 - 1 ∧ c.1 = b.1 - 1 ∧ c.2 = 1 - a.2 := by
  have hl := two_step_lane hab hbc
  have hab' := hab.1
  have hbc' := hbc.1
  omega

theorem top_diamond {a b c d e f g : Node}
    (hab : Edge a b) (hbc : Edge b c) (hcd : Edge c d)
    (hde : Edge d e) (hef : Edge e f) (hga : Edge g a)
    (ha : a.1 ≤ c.1) (hb : b.1 ≤ c.1) (hd : d.1 ≤ c.1)
    (he : e.1 ≤ c.1) (hf : f.1 ≤ c.1) (hg : g.1 ≤ c.1) :
    e = a ∨ f = b ∨ g = d := by
  have hbd := maximal_turn hbc hcd hb hd
  have hae := two_step_lane hcd hde
  have hac := two_step_lane hab hbc
  have hbf := two_step_lane hde hef
  have hgb := two_step_lane hga hab
  have hab' := hab.1
  have hde' := hde.1
  have hef' := hef.1
  have hga' := hga.1
  by_cases hsame : e.1 = a.1
  · left
    exact Prod.ext hsame (by omega)
  · by_cases hetop : e.1 = c.1
    · right
      left
      apply Prod.ext <;> omega
    · right
      right
      apply Prod.ext <;> omega

theorem maximal_cycle_four {α : Type} (next prev : α → α) (node : α → Node)
    (hinj : Function.Injective node)
    (hprev : ∀ a, next (prev a) = a)
    (hnext : Function.Injective next)
    (hedge : ∀ a, Edge (node a) (node (next a)))
    (q : α) (hmax : ∀ a, (node a).1 ≤ (node q).1) :
    next (next (next (next q))) = q := by
  let a := prev (prev q)
  let b := prev q
  let d := next q
  let e := next d
  let f := next e
  let g := prev a
  have hab : next a = b := hprev b
  have hbc : next b = q := hprev q
  have hga : next g = a := hprev a
  have heq := top_diamond
    (show Edge (node a) (node b) by simpa only [hab] using hedge a)
    (show Edge (node b) (node q) by simpa only [hbc] using hedge b)
    (hedge q) (hedge d) (hedge e)
    (show Edge (node g) (node a) by simpa only [hga] using hedge g)
    (hmax a) (hmax b) (hmax d) (hmax e) (hmax f) (hmax g)
  have hea : e = a := by
    rcases heq with h | h | h
    · exact hinj h
    · exact hnext ((hinj h).trans hab.symm)
    · have hgd : g = d := hinj h
      have := congrArg next hgd
      simpa only [hga] using this.symm
  change next (next e) = q
  rw [hea, hab, hbc]


def nextIndex {n : Nat} (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.val+1 < n then ⟨i.val+1,h⟩ else ⟨0,hn⟩

def prevIndex {n : Nat} (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.val = 0 then ⟨n-1,by omega⟩ else ⟨i.val-1,by omega⟩

theorem next_prev_index {n : Nat} (hn : 0 < n) (i : Fin n) :
    nextIndex hn (prevIndex hn i) = i := by
  by_cases hi : i.val = 0
  · have hsub : n-1+1=n := by omega
    apply Fin.ext
    simp [nextIndex,prevIndex,hi,hsub]
  · have hsub : i.val-1+1=i.val := by omega
    apply Fin.ext
    simp [nextIndex,prevIndex,hi,hsub,i.isLt]

theorem prev_next_index {n : Nat} (hn : 0 < n) (i : Fin n) :
    prevIndex hn (nextIndex hn i) = i := by
  apply Fin.ext
  dsimp [nextIndex,prevIndex]
  split <;> split <;> simp_all <;> omega

theorem prev_index_injective {n : Nat} (hn : 0 < n) : Function.Injective (prevIndex hn) := by
  intro i j he
  have h := congrArg (nextIndex hn) he
  simpa only [next_prev_index] using h

theorem nextIndex_mod {n : Nat} (hn : 0 < n) (i : Fin n) :
    nextIndex hn i = ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩ := by
  apply Fin.ext
  dsimp [nextIndex]
  split
  · rename_i h
    simp [Nat.mod_eq_of_lt h]
  · have he : i.val+1=n := by omega
    simp [he]

theorem finite_reverse_cycle_four {n : Nat} (hn : 0 < n) (node : Fin n → Node)
    (hinj : Function.Injective node)
    (hedge : ∀ i, Edge (node (nextIndex hn i)) (node i)) :
    ∃ q : Fin n, prevIndex hn (prevIndex hn (prevIndex hn (prevIndex hn q))) = q := by
  let xs := List.finRange n
  have hqmem : (⟨0,hn⟩ : Fin n) ∈ xs := List.mem_finRange _
  let q := xs.maxOn (fun i => (node i).1) (List.ne_nil_of_mem hqmem)
  have hmax : ∀ i, (node i).1 ≤ (node q).1 := by
    intro i
    exact List.le_apply_maxOn_of_mem (f := fun j => (node j).1) (List.mem_finRange i)
  refine ⟨q, maximal_cycle_four (prevIndex hn) (nextIndex hn) node hinj
    (prev_next_index hn) (prev_index_injective hn) ?_ q hmax⟩
  intro i
  simpa only [next_prev_index] using hedge (prevIndex hn i)


end LangtonsAnt.PersistA.TwoLaneCycle
