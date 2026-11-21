import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1983 : checkSingleBlackFast2 (-73, -49) 15095 .west (23, 34) (-53, 15) = true := by
  decide +kernel

end LangtonsAnt
