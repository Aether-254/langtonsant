import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0555 : checkSingleBlackFast (18, -8) 8388 .south (-9, -2) (-23, 0) = true := by
  decide +kernel

end LangtonsAnt
