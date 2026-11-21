import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0345 : checkSingleBlackFast (-3, 14) 4908 .south (-8, -9) (-18, -11) = true := by
  decide +kernel

end LangtonsAnt
