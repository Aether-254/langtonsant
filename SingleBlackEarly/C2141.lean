import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2141 : checkSingleBlackFast (-84, -65) 22168 .north (44, 40) (-70, -32) = true := by
  decide +kernel

end LangtonsAnt
