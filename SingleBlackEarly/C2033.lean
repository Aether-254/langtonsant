import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2033 : checkSingleBlackFast (-75, -56) 76169 .east (41, 22) (-72, 6) = true := by
  decide +kernel

end LangtonsAnt
