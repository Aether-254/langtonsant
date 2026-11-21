import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1739 : checkSingleBlackFast2 (-50, -28) 18403 .east (15, 9) (-18, -27) = true := by
  decide +kernel

end LangtonsAnt
