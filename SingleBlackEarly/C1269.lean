import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1269 : checkSingleBlackFast (3, 20) 9967 .east (-3, -1) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
