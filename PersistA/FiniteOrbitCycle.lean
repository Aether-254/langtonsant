import BoundedMemory

namespace LangtonsAnt.PersistA.FiniteOrbitCycle

def orbit {α : Type} (f : α → α) (a : α) : Nat → α
  | 0 => a
  | n+1 => f (orbit f a n)

theorem orbit_add {α : Type} (f : α → α) (a : α) (n k : Nat) :
    orbit f a (n+k) = orbit f (orbit f a n) k := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
      change f (orbit f a (n+k)) = f (orbit f (orbit f a n) k)
      exact congrArg f ih

theorem orbit_mem {α : Type} (xs : List α) (f : α → α)
    (hf : ∀ a ∈ xs, f a ∈ xs) {a : α} (ha : a ∈ xs) (n : Nat) :
    orbit f a n ∈ xs := by
  induction n with
  | zero => exact ha
  | succ n ih => exact hf _ ih

theorem exists_return {α : Type} (xs : List α) (f : α → α)
    (hf : ∀ a ∈ xs, f a ∈ xs) {a : α} (ha : a ∈ xs) :
    ∃ n, 0 < n ∧ ∃ b ∈ xs, orbit f b n = b := by
  obtain ⟨i,j,hij,he⟩ := finite_list_repeats xs (orbit f a) (orbit_mem xs f hf ha)
  refine ⟨j-i, by omega, orbit f a i, orbit_mem xs f hf ha i, ?_⟩
  rw [← orbit_add, Nat.add_sub_cancel' (by omega : i ≤ j)]
  exact he.symm

theorem exists_simple_cycle {α : Type} (xs : List α) (f : α → α)
    (hf : ∀ a ∈ xs, f a ∈ xs) {a : α} (ha : a ∈ xs) :
    ∃ n : Nat, ∃ hn : 0 < n, ∃ c : Fin n → α,
      Function.Injective c ∧ (∀ i, c i ∈ xs) ∧
      (∀ i, f (c i) = c ⟨(i.val+1)%n, Nat.mod_lt _ hn⟩) := by
  classical
  let property := fun n => 0 < n ∧ ∃ b ∈ xs, orbit f b n = b
  have hex : ∃ n, property n := exists_return xs f hf ha
  have hleast : ∀ k, property k → ∃ n, property n ∧ ∀ j, property j → n ≤ j := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro hk
        by_cases smaller : ∃ j, j < k ∧ property j
        · obtain ⟨j,hj,hp⟩ := smaller
          exact ih j hj hp
        · refine ⟨k,hk,?_⟩
          intro j hj
          by_cases hle : k ≤ j
          · exact hle
          · exact False.elim (smaller ⟨j,by omega,hj⟩)
  obtain ⟨k,hk⟩ := hex
  obtain ⟨n,hn,hmin⟩ := hleast k hk
  obtain ⟨hnpos,b,hb,hret⟩ := hn
  let c : Fin n → α := fun i => orbit f b i.val
  have hinj : Function.Injective c := by
    intro i j hij
    apply Fin.ext
    by_cases he : i.val = j.val
    · exact he
    have bad : ∀ (s t : Fin n), s.val < t.val → c s = c t → False := by
      intro s t hst hsame
      have hr : orbit f (orbit f b s.val) (t.val-s.val) = orbit f b s.val := by
        rw [← orbit_add, Nat.add_sub_cancel' (by omega : s.val ≤ t.val)]
        exact hsame.symm
      have hp : property (t.val-s.val) :=
        ⟨by omega, orbit f b s.val, orbit_mem xs f hf hb s.val, hr⟩
      have hnle := hmin (t.val-s.val) hp
      omega
    by_cases hijlt : i.val < j.val
    · exact False.elim (bad i j hijlt hij)
    · exact False.elim (bad j i (by omega) hij.symm)
  refine ⟨n, hnpos, c, hinj, (fun i => orbit_mem xs f hf hb i.val), ?_⟩
  intro i
  change orbit f b (i.val+1) = orbit f b ((i.val+1)%n)
  by_cases hlt : i.val+1 < n
  · rw [Nat.mod_eq_of_lt hlt]
  · have he : i.val+1=n := by omega
    rw [he, Nat.mod_self]
    exact hret


end LangtonsAnt.PersistA.FiniteOrbitCycle
