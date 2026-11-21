import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2156 : checkSingleBlackFast2 (-88, -64) 15867 .west (31, 41) (-60, 21) = true := by
  decide +kernel

end LangtonsAnt
