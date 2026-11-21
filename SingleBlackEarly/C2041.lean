import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2041 : checkSingleBlackFast (-79, -51) 25737 .east (35, 23) (13, -58) = true := by
  decide +kernel

end LangtonsAnt
