import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1867 : checkSingleBlackFast2 (-62, -37) 18019 .east (19, 22) (-3, -39) = true := by
  decide +kernel

end LangtonsAnt
