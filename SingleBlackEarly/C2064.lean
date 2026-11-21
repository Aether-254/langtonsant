import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2064 : checkSingleBlackFast (-79, -54) 21895 .east (42, 21) (-4, -60) = true := by
  decide +kernel

end LangtonsAnt
