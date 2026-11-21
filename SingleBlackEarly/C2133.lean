import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2133 : checkSingleBlackFast2 (-86, -63) 15719 .west (30, 40) (-59, 20) = true := by
  decide +kernel

end LangtonsAnt
