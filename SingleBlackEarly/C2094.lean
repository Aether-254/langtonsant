import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2094 : checkSingleBlackFast2 (-81, -60) 15898 .north (34, 22) (-61, -33) = true := by
  decide +kernel

end LangtonsAnt
