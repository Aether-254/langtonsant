import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0168 : checkSingleBlackFast (-4, 7) 5050 .south (-9, -1) (-18, -8) = true := by
  decide +kernel

end LangtonsAnt
