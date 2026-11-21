import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1701 : checkSingleBlackFast (-44, -25) 20088 .north (24, 20) (-50, -12) = true := by
  decide +kernel

end LangtonsAnt
