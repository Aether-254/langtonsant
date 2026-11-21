import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0284 : checkSingleBlackFast (16, 10) 6940 .south (-14, -8) (-22, -4) = true := by
  decide +kernel

end LangtonsAnt
