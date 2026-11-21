import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0478 : checkSingleBlackFast (-3, 7) 6265 .west (-13, -2) (-14, -20) = true := by
  decide +kernel

end LangtonsAnt
