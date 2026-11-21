import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2049 : checkSingleBlackFast2 (-79, -55) 15407 .west (26, 37) (-56, 18) = true := by
  decide +kernel

end LangtonsAnt
