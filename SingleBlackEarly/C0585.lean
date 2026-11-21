import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0585 : checkSingleBlackFast (20, 4) 6340 .south (-13, -1) (-19, -11) = true := by
  decide +kernel

end LangtonsAnt
