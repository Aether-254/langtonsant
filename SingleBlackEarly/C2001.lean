import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2001 : checkSingleBlackFast2 (-74, -51) 15095 .west (24, 34) (-53, 14) = true := by
  decide +kernel

end LangtonsAnt
