import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1943 : checkSingleBlackFast (-66, -47) 21232 .north (35, 31) (-61, -23) = true := by
  decide +kernel

end LangtonsAnt
