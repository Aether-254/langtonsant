import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1279 : checkSingleBlackFast (1, 22) 11339 .east (-3, -5) (-16, -19) = true := by
  decide +kernel

end LangtonsAnt
