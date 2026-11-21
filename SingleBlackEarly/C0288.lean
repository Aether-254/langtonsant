import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0288 : checkSingleBlackFast (13, 12) 7608 .south (-10, -1) (-18, -17) = true := by
  decide +kernel

end LangtonsAnt
