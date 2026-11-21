import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0691 : checkSingleBlackFast (19, -12) 7758 .south (-17, 2) (-22, -9) = true := by
  decide +kernel

end LangtonsAnt
