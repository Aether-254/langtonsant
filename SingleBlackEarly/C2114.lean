import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2114 : checkSingleBlackFast (-85, -62) 20893 .east (40, 25) (17, -59) = true := by
  decide +kernel

end LangtonsAnt
