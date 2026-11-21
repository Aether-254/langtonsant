import PeriodicWordCheck12H

namespace LangtonsAnt

theorem checkNoWords_twelve : checkNoWords 12 = true := by
  apply checkNoWords_of_blocks (width := 512) (blocks := 8) (by decide) (by decide)
  intro k hk
  have he : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkNoWords_twelve_A
  · exact checkNoWords_twelve_B
  · exact checkNoWords_twelve_C
  · exact checkNoWords_twelve_D
  · exact checkNoWords_twelve_E
  · exact checkNoWords_twelve_F
  · exact checkNoWords_twelve_G
  · exact checkNoWords_twelve_H

end LangtonsAnt
