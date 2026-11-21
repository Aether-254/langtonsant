import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2074 : checkSingleBlackFast (-80, -59) 20653 .east (31, 21) (15, -54) = true := by
  decide +kernel

end LangtonsAnt
