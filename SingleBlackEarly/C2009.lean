import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2009 : checkSingleBlackFast (-72, -53) 21544 .north (38, 34) (-64, -26) = true := by
  decide +kernel

end LangtonsAnt
