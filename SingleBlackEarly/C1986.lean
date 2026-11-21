import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1986 : checkSingleBlackFast (-72, -51) 20237 .east (27, 17) (11, -50) = true := by
  decide +kernel

end LangtonsAnt
