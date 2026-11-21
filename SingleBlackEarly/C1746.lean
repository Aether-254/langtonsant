import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1746 : checkSingleBlackFast (-48, -30) 27939 .east (27, 15) (-14, -37) = true := by
  decide +kernel

end LangtonsAnt
