import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2129 : checkSingleBlackFast (-87, -59) 26153 .east (39, 27) (17, -62) = true := by
  decide +kernel

end LangtonsAnt
