import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2193 : checkSingleBlackFast (-92, -66) 14292 .north (35, 27) (-61, -43) = true := by
  decide +kernel

end LangtonsAnt
