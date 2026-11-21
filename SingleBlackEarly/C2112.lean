import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2112 : checkSingleBlackFast2 (-84, -60) 15659 .west (29, 39) (-58, 19) = true := by
  decide +kernel

end LangtonsAnt
