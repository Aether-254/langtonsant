import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1263 : checkSingleBlackFast (5, 20) 10459 .east (-3, -3) (-18, -19) = true := by
  decide +kernel

end LangtonsAnt
