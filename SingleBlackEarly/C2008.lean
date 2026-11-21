import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2008 : checkSingleBlackFast (-74, -53) 20341 .east (28, 18) (12, -51) = true := by
  decide +kernel

end LangtonsAnt
