import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2170 : checkSingleBlackFast2 (-90, -62) 18657 .west (38, 44) (-64, 21) = true := by
  decide +kernel

end LangtonsAnt
