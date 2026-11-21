import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2202 : checkSingleBlackFast (-93, -70) 21309 .east (44, 29) (21, -63) = true := by
  decide +kernel

end LangtonsAnt
