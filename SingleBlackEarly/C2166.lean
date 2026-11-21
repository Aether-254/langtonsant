import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2166 : checkSingleBlackFast2 (-86, -66) 17380 .north (38, 28) (-64, -44) = true := by
  decide +kernel

end LangtonsAnt
