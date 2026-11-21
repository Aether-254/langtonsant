import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0343 : checkSingleBlackFast (-4, 13) 4276 .south (-9, -10) (-17, -10) = true := by
  decide +kernel

end LangtonsAnt
