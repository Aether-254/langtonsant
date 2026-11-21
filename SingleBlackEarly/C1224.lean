import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1224 : checkSingleBlackFast (9, 18) 9831 .east (-3, -1) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
