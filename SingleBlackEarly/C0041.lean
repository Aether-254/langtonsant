import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0041 : checkSingleBlackFast (-3, 2) 2359 .west (-3, 0) (-13, -5) = true := by
  decide +kernel

end LangtonsAnt
