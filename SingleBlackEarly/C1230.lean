import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1230 : checkSingleBlackFast (8, 20) 10343 .east (-3, -1) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
