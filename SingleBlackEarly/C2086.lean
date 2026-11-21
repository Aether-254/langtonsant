import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2086 : checkSingleBlackFast (-81, -56) 21999 .east (43, 22) (-3, -61) = true := by
  decide +kernel

end LangtonsAnt
