import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1232 : checkSingleBlackFast (7, 20) 9979 .east (-3, -1) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
