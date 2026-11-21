import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2213 : checkSingleBlackFast (-94, -67) 14280 .north (35, 27) (-61, -43) = true := by
  decide +kernel

end LangtonsAnt
