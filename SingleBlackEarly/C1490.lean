import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1490 : checkSingleBlackFast (-29, -2) 25112 .south (-4, -6) (-18, -20) = true := by
  decide +kernel

end LangtonsAnt
