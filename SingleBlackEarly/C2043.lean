import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2043 : checkSingleBlackFast2 (-78, -53) 18851 .east (27, 30) (5, -47) = true := by
  decide +kernel

end LangtonsAnt
