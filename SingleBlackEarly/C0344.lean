import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0344 : checkSingleBlackFast (-4, 14) 6427 .west (-2, 4) (-17, -10) = true := by
  decide +kernel

end LangtonsAnt
