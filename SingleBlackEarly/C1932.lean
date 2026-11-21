import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1932 : checkSingleBlackFast (-67, -42) 21271 .east (36, 15) (-10, -54) = true := by
  decide +kernel

end LangtonsAnt
